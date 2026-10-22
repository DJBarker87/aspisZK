#!/usr/bin/env python3
"""Verify retained strict-visitor build evidence; does not build Aeneas."""

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


src = ROOT / "source/InterpMatchCtxs.v3.ml"
assert sha(src) == "0d2ab7873780feaea346facc38f5429144153f6e93a08aef636509505216bb18"
assert "ty_has_regions_complete" in src.read_text()

raw = ROOT / "attempts/build-v4-gated-scope"
receipt = json.loads((raw / "receipt-reconstructed.json").read_text())
time_txt = (raw / "build.time").read_text()
assert "Command being timed: \"dune build --profile release -j 1 main.exe\"" in time_txt
assert "Exit status: 0" in time_txt
assert receipt["exit_status"] == 0 and receipt["max_rss_kib"] == 502568 and receipt["swaps"] == 0
owner = json.loads((raw / "owner-cgroup.json").read_text())
cid = (raw / "container.id").read_text().strip()
assert owner["container_id"] == cid
assert owner["proc_cgroup"].strip() == f"0::{owner['systemd_control_group']}"
assert owner["systemd_control_group"] == f"/system.slice/docker-{cid}.scope"
assert owner["cgroup_files"] == {
    "memory.high": "1073741824",
    "memory.max": "2147483648",
    "memory.swap.max": "0",
}
assert (raw / "container.memory.high").read_text().strip() == "1073741824"
assert (raw / "container.memory.max").read_text().strip() == "2147483648"
assert (raw / "container.memory.swap.max").read_text().strip() == "0"
assert receipt["strict_match_source_sha256"] == sha(src)

# The three setup attempts must remain clearly diagnostic and must not be
# relabeled as compiler runs: each has no build.time file.
for attempt in ("setup-v1-high-parent-only", "setup-v2-docker-reservation", "setup-v3-swap-limit"):
    folder = ROOT / "attempts" / attempt
    assert folder.is_dir()
    assert not (folder / "build.time").exists()

for path in ROOT.rglob("*"):
    if path.is_file():
        assert path.suffix not in {".olean", ".ilean", ".c", ".o"}, f"unexpected build artifact: {path}"

print("strict visitor source and gated cached-build evidence PASS; no Aeneas run claimed")
