import os
import re

def get_imports(filepath):
    imports = []
    try:
        with open(filepath, 'r') as f:
            for line in f:
                line = line.strip()
                if line.startswith('import '):
                    parts = line.split()
                    if len(parts) >= 2:
                        module = parts[1]
                        imports.append(module)
    except Exception as e:
        print(f"Error reading {filepath}: {e}")
    return imports

def build_graph(root_dir):
    files = {} # module_path -> absolute_path
    dependencies = {} # module_path -> [imported_modules]
    
    # First pass: find all .kk files and map module names to file paths
    # Koka module names usually match the path relative to include path.
    # Here we are in `compiler`.
    
    # We need to map "compiler/common/range" to "compiler/compiler/common/range.kk" if we are at root.
    # The workspace has `compiler/compiler/...`.
    
    for root, dirs, files_in_dir in os.walk(root_dir):
        for file in files_in_dir:
            if file.endswith(".kk"):
                abs_path = os.path.join(root, file)
                rel_path = os.path.relpath(abs_path, root_dir)
                # Remove extension and normalize separators
                module_path = os.path.splitext(rel_path)[0]
                files[module_path] = abs_path
                dependencies[module_path] = []

    # Second pass: parse imports
    for module, path in files.items():
        imps = get_imports(path)
        for imp in imps:
            # We only care about dependencies within the project (compiler folder)
            # imp is like "compiler/common/range"
            # It might match one of our keys in `files`
            if imp in files:
                dependencies[module].append(imp)
            # else:
            #    print(f"External import: {imp} in {module}")

    return dependencies, files

def print_mermaid(dependencies):
    print("graph TD")
    for mod, deps in dependencies.items():
        # sanitize names for mermaid
        safe_mod = mod.replace('/', '_').replace('-', '_').replace('.', '_')
        if not deps:
             print(f"    {safe_mod}[\"{mod}\"]")
        for dep in deps:
            safe_dep = dep.replace('/', '_').replace('-', '_').replace('.', '_')
            print(f"    {safe_mod} --> {safe_dep}")

def find_leaves(dependencies):
    # A leaf in a dependency tree (where A -> B means A depends on B)
    # is a node that has no outgoing edges (depends on nothing).
    # But usually "leaves" in a build system means "things that nobody depends on" (tops) or "things that depend on nothing" (bottoms/bases)?
    # "Dependency tree" usually means arrows point to dependencies.
    # If A imports B, A depends on B.
    # Leaves are files that don't import other files in this set.
    # But checking for unused effects implies we want to change files deepest in the dependency chain (base modules) or files at the top?
    # If I change a base module (leaf), it affects everyone importing it.
    # If the user says "starting with the leaves", they probably mean "base modules" (depends on nothing) so that changes propagate up?
    # Or "leaves" as in "nodes with no incoming edges" (top level apps)?
    
    # Re-reading prompt: "ensure that effect annotations are inferred `_` instead of explicit. This will reduce the number of effect dependencies where some effects are not actually used."
    # If `common/range.kk` (base) has `fun f() : <div,exn> int`, and `div` is not used, changing to `_` infers `<exn>`.
    # Then `type/infer.kk` which imports `range` might assume `f` has `div`. If we remove `div` from `f`, `infer` might still compile if it didn't rely on `div`.
    # So we should start from base modules (depend on nothing).
    
    leaves = [mod for mod, deps in dependencies.items() if not deps]
    return leaves

def topological_sort(dependencies):
    # Khan's algorithm adapted for "leaves first" or just standard topo sort?
    # Standard topo sort: if A depends on B, B comes before A.
    # We want to process B before A.
    # So we want an order where dependencies appear before dependents.
    
    # Graph: Node -> [Dependencies]
    # We want to visit Nodes such that for all D in Dependencies(N), D is visited before N.
    
    # Calculate in-degree (dependency count) ? No, we need to know who depends on whom?
    # Actually, we can just use the provided dependencies dict.
    # We want to output items that have no unsatisfied dependencies.
    
    visited = set()
    result = []
    
    # We can use a simple DFS post-order traversal to get a reverse topological sort (Dependents before Dependencies),
    # then reverse it.
    # Or just standard algo.
    
    def visit(node, path):
        if node in visited:
            return
        # Detect cycles if needed? Koka shouldn't have cyclic module imports hopefully.
        visited.add(node)
        for dep in dependencies.get(node, []):
             visit(dep, path)
        result.append(node)
        
    sorted_keys = sorted(dependencies.keys())
    for node in sorted_keys:
        visit(node, set())
        
    return result

if __name__ == "__main__":
    deps, files = build_graph(".")
    sorted_files = topological_sort(deps)
    for f in sorted_files:
        if f in files:
            print(files[f])
