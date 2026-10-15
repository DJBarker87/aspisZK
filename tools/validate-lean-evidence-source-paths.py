#!/usr/bin/env python3
"""Validate repository source_path entries against evidence snapshots.

Usage: python3 tools/validate-lean-evidence-source-paths.py <bundle-dir>

This read-only check prevents Lean module names (for example, R1Foo) from
being mistaken for repository filenames when the source file is Foo.lean.
"""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__.strip(), file=sys.stderr)
        return 2

    repo = Path(__file__).resolve().parents[1]
    bundle = Path(sys.argv[1]).resolve()
    manifest_path = bundle / "source-manifest.json"
    if not manifest_path.is_file():
        print(f"missing manifest: {manifest_path}", file=sys.stderr)
        return 2

    manifest = json.loads(manifest_path.read_text())
    targets = manifest.get("targets")
    if not isinstance(targets, dict) or not targets:
        print("expected a nonempty dictionary of target source pins", file=sys.stderr)
        return 2
    failures: list[str] = []
    checked = 0
    for target, entry in targets.items():
        if not isinstance(entry, dict):
            failures.append(f"{target}: expected a target pin object")
            continue
        rel = entry.get("source_path")
        expected = entry.get("source_sha256")
        snapshot_rel = entry.get("snapshot")
        if not rel or not expected:
            failures.append(f"{target}: missing source_path/source_sha256")
            continue
        source = repo / rel
        if not source.is_file():
            failures.append(f"{target}: repository source does not exist: {rel}")
            continue
        actual = sha256(source)
        if actual != expected:
            failures.append(
                f"{target}: repository source hash {actual} != manifest {expected}"
            )
            continue
        if snapshot_rel:
            snapshot = bundle / snapshot_rel
            if not snapshot.is_file():
                failures.append(f"{target}: missing bundle snapshot: {snapshot_rel}")
                continue
            snapshot_hash = sha256(snapshot)
            if snapshot_hash != expected:
                failures.append(
                    f"{target}: snapshot hash {snapshot_hash} != manifest {expected}"
                )
                continue
        checked += 1

    print(f"checked {checked} target source paths in {bundle}")
    if failures:
        for failure in failures:
            print(f"ERROR: {failure}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
