#!/usr/bin/env python3
"""Summarise an xctrace Time Profiler export.

    xctrace record --template 'Time Profiler' --output T.trace --launch -- <bin> <args>
    xctrace export --input T.trace \
        --xpath '/trace-toc/run[@number="1"]/data/table[@schema="time-profile"]' \
        --output tp.xml
    scripts/profile-report.py tp.xml

Three views, because each answers a different question:
  self      which symbol is executing        -> what to optimise
  modules   which module owns the samples    -> where it lives
  category  alloc / free / refcount split    -> whether it is memory traffic

Use the `time-profile` schema, NOT `time-sample` (raw addresses). Nodes are
shared by id/ref, so both must be resolved.
"""
import xml.etree.ElementTree as ET, collections, sys, re

ALLOC = ("mi_page_malloc","mi_theap_malloc","mi_heap_malloc","mi_malloc",
         "kk_block_alloc","kk_bytes_alloc","kk_ref_alloc","mi_generic_malloc")
FREE  = ("mi_free","mi_page_free","kk_block_drop_free","kk_block_fast_drop_free","kk_free")
RC    = ("kk_block_refcount","kk_block_check_drop","kk_block_check_dup","kk_block_dup",
         "kk_block_decref","kk_block_drop","kk_integer_dup","kk_block_refcount_set",
         "kk_dup","kk_drop")

def category(n):
    for p in ALLOC:
        if n.startswith(p): return "alloc"
    for p in FREE:
        if n.startswith(p): return "free"
    for p in RC:
        if n.startswith(p): return "refcount"
    return None

def module_of(n):
    if n.startswith("kk_compiler_") or n.startswith("kk_std_"):
        parts = n.split("_")
        return "/".join(parts[1:4]) if len(parts) > 3 else n
    return None

def rows(path):
    frames, btraces, tagged, weights = {}, {}, {}, {}
    def names_of(bt):
        r = bt.get("ref")
        if r is not None: return btraces.get(r, [])
        ns = []
        for f in bt.findall("frame"):
            fr = f.get("ref")
            if fr is not None: ns.append(frames.get(fr, "?"))
            else:
                nm = f.get("name") or "?"
                if f.get("id"): frames[f.get("id")] = nm
                ns.append(nm)
        if bt.get("id"): btraces[bt.get("id")] = ns
        return ns
    for _, el in ET.iterparse(path, events=("end",)):
        if el.tag != "row": continue
        w = el.find("weight"); ms = 0.0
        if w is not None:
            r = w.get("ref")
            if r is not None: ms = weights.get(r, 0.0)
            else:
                try: ms = float(w.text) / 1e6
                except Exception: ms = 0.0
                if w.get("id"): weights[w.get("id")] = ms
        tb = el.find("tagged-backtrace"); ns = []
        if tb is not None:
            r = tb.get("ref")
            if r is not None: ns = tagged.get(r, [])
            else:
                bt = tb.find("backtrace")
                ns = names_of(bt) if bt is not None else []
                if tb.get("id"): tagged[tb.get("id")] = ns
        yield ms, ns
        el.clear()


# DO NOT add a stage/call-tree breakdown here from the backtraces. It was tried
# and it produces phantom numbers. On a warm rebuild that source-parses exactly
# ONE two-line file, an inclusive walk of the ancestor frames attributes 568ms
# (26% of the run) to `syntax/parse/parse_program_from_string`, 277ms of it
# under `discover_deps -> scan_deps`. Three independent checks say that chain
# never ran:
#   1. the port's own dep-cache reports 26/26 modules satisfied from .kki with
#      zero scan-deps calls (scripts/disc-probe.kk)
#   2. lexing -- which any real source parse must do first -- owns 85ms total,
#      far too little for 26 std/core sources
#   3. `syntax/parse` owns only 58ms (2.6%) of INNERMOST frame time
# A single `_trmc_` symbol also repeats up to 255x in one backtrace.
#
# So ancestor frames in this binary are not trustworthy (stale stack words
# and/or nearest-preceding-symbol resolution of local symbols). What survives
# scrutiny is leaf-anchored: SELF, CATEGORY, and BY MODULE (which attributes to
# the INNERMOST owning frame). For a real call breakdown use source-level phase
# timing, or -finstrument-functions (see docs/koka-perf-debugging.md) -- gprof
# is not an option on macOS (-pg links but emits no gmon.out) and XRay produces
# no log here.
def stack_sanity(rows_list, total):
    worst = collections.Counter()
    for _ms, ns in rows_list:
        c = collections.Counter(n for n in ns if "_trmc_" in n)
        for n, k in c.items():
            if k > worst[n]: worst[n] = k
    if not worst: return
    print("\n=== STACK TRUST CHECK (deepest repeat of one _trmc_ symbol)")
    for n, k in worst.most_common(3):
        print("  %3dx  %s" % (k, n[:78]))
    print("  ancestor frames are unreliable here -- trust SELF/CATEGORY/BY MODULE,")
    print("  not an inclusive or call-tree reading. See the comment above.")

def main():
    path = sys.argv[1]
    self_ms  = collections.Counter()
    incl     = collections.Counter()
    mod_all  = collections.Counter()
    mod_mem  = collections.Counter()
    cat      = collections.Counter()
    cat_who  = {"alloc": collections.Counter(), "free": collections.Counter(),
                "refcount": collections.Counter()}
    total = 0.0
    kept = []
    for ms, ns in rows(path):
        total += ms
        if not ns: continue
        kept.append((ms, ns))
        leaf = ns[0]
        self_ms[leaf] += ms
        for f in dict.fromkeys(ns):   # inclusive: each frame once per sample
            incl[f] += ms
        owner = next((module_of(n) for n in ns if module_of(n)), None)
        if owner:
            mod_all[owner] += ms
            if category(leaf): mod_mem[owner] += ms
        k = category(leaf)
        if k:
            cat[k] += ms
            who = next((n for n in ns if n.startswith("kk_compiler_")
                        or (n.startswith("kk_std_") and "_hnd_" not in n)), "?")
            cat_who[k][who] += ms
    pct = lambda v: 100 * v / total if total else 0
    print("TOTAL %.0fms\n" % total)
    print("=== SELF (top 20)")
    for n, v in self_ms.most_common(20):
        print("  %8.0fms %5.1f%%  %s" % (v, pct(v), n[:96]))
    print("\n=== INCLUSIVE (top 18 compiler/std frames)  -- UNRELIABLE, see stack check")
    for n, v in incl.most_common(400):
        if not (n.startswith("kk_compiler_") or n.startswith("kk_std_")): continue
        if pct(v) < 1.0: continue
        print("  %8.0fms %5.1f%%  %s" % (v, pct(v), n[:92]))
    stack_sanity(kept, total)
    print("\n=== BY MODULE (top 12)   [mem = alloc/free/refcount leaves]")
    for n, v in mod_all.most_common(12):
        print("  %8.0fms %5.1f%%  mem %5.1f%%  %s"
              % (v, pct(v), 100 * mod_mem[n] / v if v else 0, n))
    print("\n=== CATEGORY")
    for k in ("alloc", "free", "refcount"):
        print("  %-9s %8.0fms %5.1f%%" % (k, cat[k], pct(cat[k])))

    # Alloc and free attributed to the same owning caller, side by side.
    # A caller that does BOTH is a reuse (FBIP) candidate -- it tears a value
    # down and builds one straight after, so the block could be handed over
    # instead of returned to the allocator. A caller that only frees is not:
    # its allocation happened somewhere else, which is a harder optimisation.
    # Refcount is the LARGEST category and upstream pays comparable memory
    # traffic overall, so the interesting question is never "is there memory
    # traffic" but WHERE it is and what stops a block being reused. Attribute
    # the refcount leaves the same way.
    print("\n=== REFCOUNT by owning caller (top 16)")
    for n, v in cat_who["refcount"].most_common(16):
        print("  %8.0fms %5.1f%%  %s" % (v, pct(v), n[:82]))

    print("\n=== ALLOC vs FREE by owning caller (top 20 by combined)")
    owners = set(cat_who["alloc"]) | set(cat_who["free"])
    rank = sorted(owners, key=lambda n: -(cat_who["alloc"][n] + cat_who["free"][n]))
    print("  %9s %9s  %-6s %s" % ("alloc", "free", "kind", "caller"))
    for n in rank[:20]:
        a, f = cat_who["alloc"][n], cat_who["free"][n]
        kind = "REUSE?" if a > 0 and f > 0 else ("free" if f > 0 else "alloc")
        print("  %7.0fms %7.0fms  %-6s %s" % (a, f, kind, n[:72]))

main()
