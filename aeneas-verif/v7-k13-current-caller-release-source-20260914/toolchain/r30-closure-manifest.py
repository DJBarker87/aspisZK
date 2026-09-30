#!/usr/bin/env python3
"""Freeze/check the exact local and deterministically staged terminal closure.

Arithmetic/Aeneas/Mathlib dependencies remain the separately pinned build cache.
No broad filesystem search or dependency build is performed.
"""
import argparse
import hashlib
import re
from pathlib import Path

TARGET = "V7ProductionSnapshotObserverR30ClosureAxioms"
IMPORT = re.compile(r"^import ([A-Za-z0-9_'.]+)$", re.MULTILINE)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("bundle", type=Path)
    parser.add_argument("stage", type=Path)
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    bundle, stage = args.bundle.resolve(), args.stage.resolve()
    modules = {}
    roots = [(bundle / "generated", "generated")]
    roots += [(bundle / directory, directory) for directory in
              ("proof-r26", "proof-r28", "proof-r30")]
    roots += [(stage, "staged-r29")]
    for root, prefix in roots:
        for path in sorted(root.rglob("*.lean")):
            if path.name.endswith("_Template.lean") or path.name.endswith(".raw.lean"):
                continue
            relative = path.relative_to(root)
            module = relative.with_suffix("").as_posix().replace("/", ".")
            if module in modules:
                raise RuntimeError(f"duplicate module {module}")
            modules[module] = (path, f"{prefix}/{relative.as_posix()}")
    order, done, active, external = [], set(), set(), set()

    def visit(module):
        if module in done:
            return
        if module in active:
            raise RuntimeError(f"import cycle {module}")
        active.add(module)
        path, _ = modules[module]
        source = path.read_text()
        if re.search(r"\b(sorry|admit|native_decide)\b|^\s*axiom\s", source, re.MULTILINE):
            raise RuntimeError(f"forbidden proof shortcut: {path}")
        for dependency in IMPORT.findall(source):
            if dependency in modules:
                visit(dependency)
            elif dependency.startswith(("V7CallerCurrentReleaseR26", "V7Production", "V7Gamma", "V7Qm31")):
                raise RuntimeError(f"missing source dependency {dependency}")
            else:
                external.add(dependency)
        active.remove(module)
        done.add(module)
        order.append(module)

    visit(TARGET)
    manifest, rows = [], []
    for module in order:
        path, relative = modules[module]
        manifest.append(f"{hashlib.sha256(path.read_bytes()).hexdigest()}  {relative}\n")
        rows.append(f"{module}\t{relative}\n")
    for relative in ("toolchain/stage-r29-production-callbacks.py",
                     "toolchain/r30-closure-manifest.py", "replay-r30-closure-manifest.sh"):
        manifest.append(f"{hashlib.sha256((bundle / relative).read_bytes()).hexdigest()}  {relative}\n")
    artifacts = {
        "R30-CLOSURE-MANIFEST.sha256": "".join(manifest),
        "R30-CLOSURE-ORDER.tsv": "".join(rows),
        "R30-CLOSURE-EXTERNALS.txt": "".join(f"{module}\n" for module in sorted(external)),
    }
    for name, expected in artifacts.items():
        path = bundle / name
        if args.write:
            path.write_text(expected)
        elif path.read_text() != expected:
            raise RuntimeError(f"frozen closure mismatch: {path}")
    print(f"CLOSURE target={TARGET} modules={len(order)} externals={len(external)} mode={'write' if args.write else 'check'}")


if __name__ == "__main__":
    main()
