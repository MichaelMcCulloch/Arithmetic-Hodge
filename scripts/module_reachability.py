#!/usr/bin/env python3
"""Audit which ArithmeticHodge modules the root build target actually covers.

`lake build` verifies only the import closure of the root `ArithmeticHodge.lean`.
A module on disk but outside that closure is silently unverified by the default
target. This script reports the closure, the orphans, and any orphan that a
reachable module imports (which would be a broken build).

Usage: python3 scripts/module_reachability.py [--list]
"""

import os
import re
import sys


def main() -> None:
    imports: dict[str, list[str]] = {}
    for root, dirs, files in os.walk("ArithmeticHodge"):
        dirs[:] = [d for d in dirs if d != ".lake"]
        for fn in files:
            if fn.endswith(".lean"):
                path = os.path.join(root, fn)
                mod = path[:-5].replace("/", ".")
                with open(path) as f:
                    imports[mod] = re.findall(
                        r"^import (ArithmeticHodge\.\S+)", f.read(), re.M
                    )

    with open("ArithmeticHodge.lean") as f:
        stack = re.findall(r"^import (ArithmeticHodge\.\S+)", f.read(), re.M)

    seen: set[str] = set()
    while stack:
        mod = stack.pop()
        if mod not in seen:
            seen.add(mod)
            stack.extend(imports.get(mod, []))

    on_disk = set(imports)
    unreachable = sorted(on_disk - seen)
    broken = [
        (mod, imp)
        for mod in sorted(seen & on_disk)
        for imp in imports[mod]
        if imp not in seen and imp in on_disk
    ]

    print(f"modules on disk:     {len(on_disk)}")
    print(f"reachable from root: {len(seen & on_disk)}")
    print(f"unreachable:         {len(unreachable)}")
    print(f"reachable importing unreachable (must be 0): {len(broken)}")
    for mod, imp in broken:
        print(f"  BROKEN: {mod} -> {imp}")
    if "--list" in sys.argv:
        for mod in unreachable:
            print(mod)
    sys.exit(1 if broken else 0)


if __name__ == "__main__":
    main()
