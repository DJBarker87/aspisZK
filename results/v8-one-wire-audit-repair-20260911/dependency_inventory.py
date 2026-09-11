#!/usr/bin/env python3
"""Conservative source inventory for the promoted V8 audit roots.

This is deliberately not a build-system replacement.  It records only a
source-file resolution made from the pinned checkout roots, and labels every
unresolved import rather than treating cached .olean files as rebuilt source.
"""
from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXPERIMENTS = ROOT / "docs/research/v8-no-work-100-20260907/experiments"
FORMAL = ROOT / "AspisFormal/AspisFormal"
IMPORT = re.compile(r"^import\s+([A-Za-z0-9_.]+)\s*$", re.M)

def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def resolve(module: str) -> Path | None:
    formal_module = module.removeprefix("AspisFormal.")
    candidates = [
        EXPERIMENTS / f"{module}.lean",
        EXPERIMENTS / (module.replace(".", "/") + ".lean"),
        FORMAL / (formal_module.replace(".", "/") + ".lean"),
    ]
    for candidate in candidates:
        if candidate.is_file():
            return candidate
    return None

def walk(module: str, visited: dict[str, dict], unresolved: set[str]) -> None:
    if module in visited:
        return
    path = resolve(module)
    if path is None:
        unresolved.add(module)
        return
    text = path.read_text()
    imports = IMPORT.findall(text)
    visited[module] = {
        "path": str(path.relative_to(ROOT)),
        "sha256": digest(path),
        "imports": imports,
    }
    for imported in imports:
        walk(imported, visited, unresolved)

def main() -> int:
    roots = sys.argv[1:] or [
        "SuccessfulCompleteSelectedWire",
        "OneWireConsumedFields",
    ]
    visited: dict[str, dict] = {}
    unresolved: set[str] = set()
    for root in roots:
        walk(root, visited, unresolved)
    print(json.dumps({
        "schema": "aspis-v8-source-inventory/v1",
        "roots": roots,
        "checkout": str(ROOT),
        "source_modules": visited,
        "unresolved_imports": sorted(unresolved),
        "verdict": "inventory only; unresolved imports may be third-party or Lake-root modules; this is not a clean source rebuild",
    }, indent=2, sort_keys=True))
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
