#!/usr/bin/env python3
"""Stage selected Lean objects and SAME-owner companions without building anything.

Input: {"owners": {"Module.Name": {"path": ".../Name.olean", "sha256": "..."}}}.
Only explicitly selected owners are copied. Companions include .olean.server,
.olean.private and .ir when present beside that exact original .olean.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def stage(selection: Path, output: Path, record: Path) -> dict:
    owners = json.loads(selection.read_text())["owners"]
    files = []
    for module, owner in sorted(owners.items()):
        if not re.fullmatch(r"[A-Za-z0-9_]+(?:\.[A-Za-z0-9_]+)*", module):
            raise ValueError(f"Invalid module name: {module!r}")
        source = Path(owner["path"])
        if source.suffix != ".olean" or digest(source) != owner["sha256"]:
            raise ValueError(f"Selected original object hash mismatch: {source}")
        target = output / (module.replace(".", "/") + ".olean")
        pairs = [(source, target)]
        for suffix in (".server", ".private"):
            pairs.append((Path(str(source) + suffix), Path(str(target) + suffix)))
        pairs.append((source.with_suffix(".ir"), target.with_suffix(".ir")))
        for original, destination in pairs:
            if not original.exists():
                if destination.exists():
                    raise ValueError(f"Destination companion has no selected original; use fresh output: {destination}")
                continue
            expected = digest(original)
            destination.parent.mkdir(parents=True, exist_ok=True)
            if original.resolve() != destination.resolve():
                temporary = destination.with_name(destination.name + f".stage-{os.getpid()}")
                shutil.copy2(original, temporary)
                if digest(temporary) != expected:
                    temporary.unlink()
                    raise ValueError(f"Copy hash mismatch: {original}")
                temporary.replace(destination)
            files.append({"module": module, "source": str(original),
                          "destination": str(destination), "sha256": expected})
        if digest(source) != owner["sha256"]:
            raise ValueError(f"Original owner changed during staging: {source}")
    result = {"schema": "selected-lean-cache-with-companions-v1",
              "selection": str(selection), "output": str(output), "files": files}
    verify(result)
    record.parent.mkdir(parents=True, exist_ok=True)
    record.write_text(json.dumps(result, indent=2) + "\n")
    return result


def verify(record: dict) -> None:
    indexed = {item["source"]: item for item in record["files"]}
    for item in record["files"]:
        for key in ("source", "destination"):
            path = Path(item[key])
            if not path.is_file() or digest(path) != item["sha256"]:
                raise ValueError(f"Missing or mismatched {key}: {path}")
        original = Path(item["source"])
        if original.suffix == ".olean":
            companions = [Path(str(original) + ".server"),
                          Path(str(original) + ".private"), original.with_suffix(".ir")]
            for companion in companions:
                if companion.exists() and str(companion) not in indexed:
                    raise ValueError(f"Selected owner companion omitted: {companion}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--selection", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--record", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.check:
        result = json.loads(args.record.read_text())
        verify(result)
    else:
        if args.selection is None or args.output is None:
            parser.error("--selection and --output are required when staging")
        result = stage(args.selection, args.output, args.record)
    print(json.dumps({"status": "PASS", "files": len(result["files"]),
                      "record": str(args.record)}))


if __name__ == "__main__":
    main()
