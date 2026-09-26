#!/usr/bin/env python3
"""Report and annotate private declarations referenced from importing modules."""

import argparse
import re
from collections import defaultdict
from pathlib import Path


MODULE_RE = re.compile(r"^module\s+([^\s]+)")
IMPORT_RE = re.compile(r"^(?:pub\s+)?import\s+([^\s]+)")
DECL_RE = re.compile(
    r"^(?P<pub>pub\s+)?(?:noinline\s+|inline\s+|inlineable\s+|abstract\s+|open\s+|value\s+|co\s+|rec\s+)*"
    r"(?:(?P<eff>effect\s+))?"
    r"(?P<kind>fun|val|var|type|struct|alias|effect)\s+(?:<[^>]+>\s*)?"
    r"(?P<name>[A-Za-z0-9_/?!+*<>=|~^%&$-]+)"
)
TOKEN_RE = re.compile(r"[A-Za-z0-9_!?'-]+(?:/[A-Za-z0-9_!?'-]+)*")


def source_files(root: Path):
    return sorted(
        path
        for path in root.rglob("*.kk")
        if ".claude" not in path.parts and ".koka" not in path.parts
    )


def strip_line(line: str) -> str:
    """Remove comments and strings enough to avoid counting prose as uses."""
    line = re.sub(r'"(?:\\.|[^"\\])*"', '""', line)
    return line.split("//", 1)[0]


def collect_std_stems(std_root: Path) -> set:
    std_stems = set()
    for path in source_files(std_root):
        for line in path.read_text().splitlines():
            if line.startswith((" ", "\t")):
                continue
            match = DECL_RE.match(strip_line(line))
            if match:
                name = match.group("name")
                stem = name.rsplit("/", 1)[-1]
                std_stems.add(stem)
    return std_stems


def parse_module(path: Path, root: Path):
    lines = path.read_text().splitlines()
    module = None
    imports = []
    declarations = []
    
    for line_number, line in enumerate(lines, 1):
        clean = strip_line(line)
        if not module:
            m = MODULE_RE.match(clean)
            if m:
                module = m.group(1)
        m_imp = IMPORT_RE.match(clean)
        if m_imp:
            imports.append(m_imp.group(1))
            
        if not line.startswith((" ", "\t")):
            m_decl = DECL_RE.match(clean)
            if m_decl:
                name = m_decl.group("name")
                if not name or name.endswith("/"):
                    continue
                stem = name.rsplit("/", 1)[-1]
                qualifier = name.rsplit("/", 1)[0] if "/" in name else None
                kind = m_decl.group("kind")
                if m_decl.group("eff"):
                    kind = f"effect {kind}"
                declarations.append(
                    {
                        "name": name,
                        "stem": stem,
                        "qualifier": qualifier,
                        "kind": kind,
                        "public": bool(m_decl.group("pub")),
                        "line": line_number,
                        "raw_line": line,
                        "path": path,
                    }
                )

    if module is None:
        return None

    tokens = set()
    clean_lines = []
    for line_number, line in enumerate(lines, 1):
        clean = strip_line(line)
        clean_lines.append(clean)
        if not clean or clean.startswith((
            "module ", "import ", "pub import "
        )):
            continue
        if not line.startswith((" ", "\t")) and DECL_RE.match(clean):
            continue
        for token in TOKEN_RE.findall(clean):
            tokens.add(token)

    return {
        "module": module,
        "imports": set(imports),
        "declarations": declarations,
        "lines": lines,
        "clean_lines": clean_lines,
        "path": path,
        "tokens": tokens,
    }


def matches_role(clean_lines, stem: str, kind: str) -> bool:
    esc_stem = re.escape(stem)
    if "type" in kind or "struct" in kind or "alias" in kind:
        pattern = re.compile(
            rf"(?::|->|<|::|\btype\b|\bstruct\b|\balias\b)\s*(?:[A-Za-z0-9_/?!+*<>=|~^%&$-]+/)*{esc_stem}(?![A-Za-z0-9_!?'-])"
            rf"|(?<![A-Za-z0-9_!?'-/]){esc_stem}\s*<"
            rf"|(?<![A-Za-z0-9_!?'-/]){esc_stem}/"
        )
        return any(pattern.search(l) for l in clean_lines)
    elif "effect" in kind:
        pattern = re.compile(
            rf"<\s*(?:[^>]*\b)?{esc_stem}(?![A-Za-z0-9_!?'-])"
            rf"|\bwith\s+(?:val\s+)?{esc_stem}\b"
            rf"|\beffect\s+{esc_stem}\b"
            rf"|(?<![A-Za-z0-9_!?'-/:]){esc_stem}(?![A-Za-z0-9_!?'-])"
        )
        return any(pattern.search(l) for l in clean_lines)
    elif "fun" in kind:
        pattern = re.compile(
            rf"(?<![A-Za-z0-9_!?'-/]){esc_stem}\s*\("
            rf"|\.{esc_stem}(?![A-Za-z0-9_!?'-])"
            rf"|(?<![A-Za-z0-9_!?'-/]){esc_stem}(?![A-Za-z0-9_!?'-])"
        )
        return any(pattern.search(l) for l in clean_lines)
    elif "val" in kind or "var" in kind:
        pattern = re.compile(rf"(?<![A-Za-z0-9_!?'-/:]){esc_stem}(?![A-Za-z0-9_!?'-])")
        return any(pattern.search(l) for l in clean_lines)
    return True


def analyze(compiler_root: Path, std_root: Path):
    std_stems = collect_std_stems(std_root) if std_root.exists() else set()
    modules = [
        parsed
        for path in source_files(compiler_root)
        if (parsed := parse_module(path, compiler_root))
    ]
    mod_by_name = {m["module"]: m for m in modules}

    stems_in_module = defaultdict(set)
    decls_by_mod_stem = defaultdict(lambda: defaultdict(list))
    for m in modules:
        for d in m["declarations"]:
            d["module"] = m["module"]
            stems_in_module[m["module"]].add(d["stem"])
            decls_by_mod_stem[m["module"]][d["stem"]].append(d)

    results = []

    for provider in modules:
        prov_mod = provider["module"]
        prov_base = prov_mod.rsplit("/", 1)[-1]

        users = [
            u for u in modules
            if prov_mod in u["imports"] and u["module"] != prov_mod
        ]
        if not users:
            continue

        for d in provider["declarations"]:
            if d["public"]:
                continue

            stem = d["stem"]
            kind = d["kind"]
            in_std = stem in std_stems

            qual_name = f"{prov_base}/{stem}"
            full_qual = f"{prov_mod}/{stem}"
            type_qual = d["name"] if d["qualifier"] else None

            refs = []
            confident_witnesses = []

            for u in users:
                u_mod = u["module"]
                has_exact_qual = (
                    qual_name in u["tokens"]
                    or full_qual in u["tokens"]
                    or (type_qual and type_qual in u["tokens"])
                )
                has_stem = stem in u["tokens"]

                if not (has_exact_qual or has_stem):
                    continue

                if not matches_role(u["clean_lines"], stem, kind):
                    continue

                if has_exact_qual:
                    refs.append((u_mod, "qualified"))
                    confident_witnesses.append(u_mod)
                elif has_stem:
                    refs.append((u_mod, "unqualified"))
                    other_providers = [
                        imp for imp in u["imports"]
                        if imp != prov_mod and imp in stems_in_module and stem in stems_in_module[imp]
                    ]
                    u_defines_stem = stem in stems_in_module[u_mod]
                    if not other_providers and not u_defines_stem and not in_std:
                        confident_witnesses.append(u_mod)

            if not refs:
                continue

            if confident_witnesses:
                confidence = "DEFINITE_UNIQUE_IN_IMPORTER"
            elif in_std:
                confidence = "AMBIGUOUS_STD"
            else:
                confidence = "AMBIGUOUS_OVERLOAD"

            results.append({
                "declaration": d,
                "confidence": confidence,
                "refs": refs,
                "confident_witnesses": confident_witnesses,
                "provider": prov_mod,
            })

    return results, modules, mod_by_name


def apply_pub(declaration: dict) -> bool:
    path = declaration["path"]
    lines = path.read_text().splitlines()
    line_idx = declaration["line"] - 1
    orig_line = lines[line_idx]

    if orig_line.lstrip().startswith("pub "):
        return False

    indent = orig_line[:len(orig_line) - len(orig_line.lstrip())]
    rest = orig_line.lstrip()
    new_line = f"{indent}pub {rest}"
    lines[line_idx] = new_line
    path.write_text("\n".join(lines) + "\n")
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "root",
        nargs="?",
        type=Path,
        default=Path("compiler"),
        help="directory containing Koka modules (default: compiler)",
    )
    parser.add_argument(
        "--std",
        type=Path,
        default=Path("lib/std"),
        help="directory containing Koka std library",
    )
    parser.add_argument(
        "--single-only",
        action="store_true",
        help="only report / fix high-confidence single definitions",
    )
    parser.add_argument(
        "--fix",
        action="store_true",
        help="automatically add 'pub' to reported declarations",
    )
    args = parser.parse_args()

    results, modules, mod_by_name = analyze(args.root.resolve(), args.std.resolve())

    high_confidence = [
        r for r in results
        if r["confidence"].startswith("DEFINITE")
    ]
    ambiguous = [
        r for r in results
        if not r["confidence"].startswith("DEFINITE")
    ]

    to_report = high_confidence if args.single_only else results
    print(f"Total candidates: {len(results)}")
    print(f"High-confidence candidates: {len(high_confidence)}")
    print(f"Ambiguous candidates: {len(ambiguous)}")

    if args.fix:
        fixed_count = 0
        for item in to_report:
            if apply_pub(item["declaration"]):
                fixed_count += 1
                d = item["declaration"]
                print(f"Fixed [{item['confidence']}]: {d['module']} -> {d['kind']} {d['name']} (line {d['line']})")
        print(f"\nApplied 'pub' to {fixed_count} declarations.")
    else:
        for item in to_report:
            d = item["declaration"]
            witnesses = ", ".join(item["confident_witnesses"][:3]) if item["confident_witnesses"] else "none"
            print(f"[{item['confidence']}] {d['module']}: {d['kind']} {d['name']} (line {d['line']}) <- witnesses: {witnesses}")


if __name__ == "__main__":
    main()