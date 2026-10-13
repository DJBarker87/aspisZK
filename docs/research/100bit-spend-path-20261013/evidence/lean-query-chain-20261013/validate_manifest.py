#!/usr/bin/env python3
"""Read-only validation of the frozen focused Lean query-chain evidence."""

from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent
MANIFEST = HERE / "manifest.json"
RECEIPT_AXIOMS = {
    "[propext, Classical.choice, Quot.sound]",
    "[propext, Quot.sound]",
}
CAPS = {
    "MemoryHigh": "4G",
    "MemoryMax": "6G",
    "MemorySwapMax": "0",
}


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def fail(message: str) -> None:
    raise ValueError(message)


def main() -> int:
    manifest = json.loads(MANIFEST.read_text())
    repo = HERE.parents[4]
    problems: list[str] = []
    for entry in manifest["targets"]:
        label = f"{entry['target']} {entry['attempt']}"
        try:
            source = repo / entry["source"]
            evidence_dir = repo / entry["evidence_dir"]
            receipt_path = evidence_dir / entry["receipt"]
            sidecar_path = evidence_dir / entry["sha256_sidecar"]
            receipt = json.loads(receipt_path.read_text())
            source_hash = sha256(source)
            sidecar_hash = sidecar_path.read_text().split()[0]
            if source_hash != entry["source_sha256"]:
                fail(f"source SHA mismatch: {source_hash}")
            if source_hash != receipt.get("source_sha256"):
                fail("source SHA differs from receipt")
            if source_hash != sidecar_hash:
                fail("source SHA differs from sidecar")
            if receipt.get("target") != entry["target"]:
                fail("receipt target mismatch")
            if receipt.get("attempt") != entry["attempt"]:
                fail("receipt attempt mismatch")
            if receipt.get("exit_status") != 0:
                fail(f"nonzero receipt status: {receipt.get('exit_status')}")
            if str(receipt.get("swaps")) != "0":
                fail(f"swap use reported: {receipt.get('swaps')}")
            cgroup = receipt.get("cgroup", {})
            for key, expected in CAPS.items():
                if cgroup.get(key) != expected:
                    fail(f"unexpected {key}: {cgroup.get(key)}")

            log_text = (evidence_dir / receipt["log"]).read_text()
            axiom_lists = [re.sub(r"\s+", " ", value) for value in
                re.findall(r"depends on axioms:\s*(\[[^]]*\])", log_text)]
            expected_count = len(re.findall(r"^#print axioms ", source.read_text(), re.M))
            if len(axiom_lists) != expected_count:
                fail(f"axiom audit count mismatch: {len(axiom_lists)} vs {expected_count}")
            expected_axioms = entry["expected_axioms"]
            if not axiom_lists:
                fail("no printed axiom results found")
            if "sorryAx" in log_text:
                fail("sorryAx occurs in printed axiom results")
            if set(axiom_lists) != {expected_axioms}:
                fail(f"axiom lists differ: {sorted(set(axiom_lists))}")
            if not (evidence_dir / receipt["time_log"]).is_file():
                fail("timing log is missing")
            print(f"PASS {label}: {source_hash}; axioms={expected_axioms}")
        except Exception as exc:  # report all mismatches in one audit
            problems.append(f"FAIL {label}: {exc}")
    if problems:
        print("\n".join(problems), file=sys.stderr)
        return 1
    print(f"Validated {len(manifest['targets'])} focused target receipts.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
