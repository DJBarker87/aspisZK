"""Collect textual R20 gate evidence without rerunning any gate."""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / "evidence" / "r20-source-gates-a"
PACK = ROOT / "r20-pack"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def first_json(text: str) -> dict:
    start = text.find("{")
    if start < 0:
        return {}
    decoder = json.JSONDecoder()
    value, _ = decoder.raw_decode(text[start:])
    return value


def log_record(path: Path, manifest: Path | None) -> dict:
    text = path.read_text(errors="replace")
    command = first_json(text)
    record = {
        "log": str(path.relative_to(ROOT)),
        "stage": command.get("stage"),
        "command": command.get("command"),
        "rustflags": command.get("rustflags"),
        "exit_status": None,
        "wall_seconds": None,
        "peak_rss_kib": None,
        "swaps": None,
    }
    for line in text.splitlines():
        if line.startswith("\tExit status:"):
            record["exit_status"] = int(line.rsplit(":", 1)[1].strip())
        elif line.startswith("\tCommand exited with non-zero status"):
            record["exit_status"] = int(line.rsplit(" ", 1)[1])
        elif "Elapsed (wall clock) time" in line:
            value = re.search(r"Elapsed \(wall clock\) time \([^)]*\):\s*([0-9:.]+)", line).group(1)
            parts = value.split(":")
            if len(parts) == 3:
                record["wall_seconds"] = int(parts[0]) * 3600 + int(parts[1]) * 60 + float(parts[2])
            elif len(parts) == 2:
                record["wall_seconds"] = int(parts[0]) * 60 + float(parts[1])
        elif "Maximum resident set size" in line:
            record["peak_rss_kib"] = int(line.rsplit(":", 1)[1].strip())
        elif line.startswith("\tSwaps:"):
            record["swaps"] = int(line.rsplit(":", 1)[1].strip())
    if manifest and manifest.exists():
        data = json.loads(manifest.read_text())
        record["manifest"] = str(manifest.relative_to(ROOT))
        record["profile"] = data.get("profile")
        record["source_revision"] = data.get("source_revision")
    return record


def source_pins() -> dict:
    pins = json.loads((PACK / "SOURCE_PINS.json").read_text())
    manifest = json.loads((PACK / "MANIFEST.json").read_text())
    payload = {
        name: {
            "expected_sha256": entry["sha256"],
            "bytes": entry["bytes"],
            "observed_sha256": sha256(PACK / name),
        }
        for name, entry in manifest["files"].items()
    }
    for entry in payload.values():
        entry["match"] = entry["expected_sha256"] == entry["observed_sha256"]
    git_blobs = {}
    for name, expected in pins["git_blobs"].items():
        result = subprocess.run(
            ["git", "cat-file", "-e", f"{pins['commit']}:{name}"],
            cwd=ROOT.parent.parent.parent,
            check=False,
        )
        observed = None
        if result.returncode == 0:
            observed = subprocess.check_output(
                ["git", "rev-parse", f"{pins['commit']}:{name}"],
                cwd=ROOT.parent.parent.parent,
                text=True,
            ).strip()
        git_blobs[name] = {
            "expected": expected,
            "observed": observed,
            "match": observed == expected,
        }
    return {
        "base_commit": pins["commit"],
        "git_blobs": git_blobs,
        "git_blob_count": len(git_blobs),
        "git_blobs_all_match": all(entry["match"] for entry in git_blobs.values()),
        "payload_hashes": payload,
        "payload_hash_count": len(payload),
        "payload_all_match": all(entry["match"] for entry in payload.values()),
    }


def main() -> None:
    manifests = {
        "opening-check-a": EVIDENCE / "opening-check-a" / "r18-stage.json",
        "digest-check-d": EVIDENCE / "digest-check-d" / "r18-stage.json",
    }
    gates = []
    for subdir in sorted(EVIDENCE.iterdir()):
        if not subdir.is_dir():
            continue
        for log in sorted(subdir.glob("*.log")):
            manifest = manifests.get(subdir.name)
            gates.append(log_record(log, manifest))
    report = {
        "marker": "R20_SOURCE_GATES_A",
        "scope": "textual evidence collection only; no reruns",
        "gates": gates,
        "source_pins": source_pins(),
        "failure_interpretation": {
            "digest-check-a/b/c": "checker plumbing failures preserved; not protocol regressions",
            "dot-micro-a": "checker plumbing failure from unavailable QM31::from_m31",
            "combined-b": "checker compile typing failure in r20_sparse_whole.rs",
            "combined-d": "checker include/path failure for staged private canonical module",
        },
    }
    out = EVIDENCE / "r20-source-gates-a.json"
    out.write_text(json.dumps(report, indent=2) + "\n")
    print(f"wrote {out} ({len(gates)} log records; {len(report['source_pins']['payload_hashes'])} payload hashes)")


if __name__ == "__main__":
    main()
