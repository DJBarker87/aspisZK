#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, subprocess

root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
expected={"kani-v7":"a5f11a27423efcf797523d7f1cc1d70e335b2c29d27229525b8571c9525a919a",
          "kani-v9":"c5fe1ab41866c6a2dce9e618ea955e039134d0309cda764c758edaa87fbc5daa",
          "kani-q-v2":"33388a99f87c9e17f6738ffb1ffecb57648a7cd26a1fe6cca15e9ccddf941294"}
for run,source_sha in expected.items():
    receipt=json.loads((root/run/"receipt.json").read_text())
    pre=json.loads((root/run/"preflight.json").read_text())
    assert receipt["exit_status"]==0 and receipt["watchdog_abort"] is None
    assert receipt["source_sha256"]==source_sha==pre["source_sha256"]
    assert receipt["limits"]=={"memory.high":"2147483648","memory.max":"4294967296","memory.swap.max":"0"}
    assert receipt["swaps"]==0 and receipt["scope_swap_peak_bytes"]==0
    assert json.loads((root/run/"admission.json").read_text())["allowed"] is True
    assert "VERIFICATION:- SUCCESSFUL" in (root/run/"kani.log").read_text()
assert sha(root/"src/lib.rs")==expected["kani-v7"]
assert sha(root/"src-n29.rs")==expected["kani-v9"]
assert sha(root/"src-q-v2.rs")==expected["kani-q-v2"]
assert json.loads((root/"kani-v8/admission.json").read_text())["allowed"] is True
assert "JSONDecodeError" in (root/"kani-v8/scope.stderr.log").read_text()
assert json.loads((root/"kani-q-v1/receipt.json").read_text())["exit_status"]==1
subprocess.run(["python3",str(root/"check-q-source.py")],check=True,stdout=subprocess.DEVNULL)
subprocess.run(["python3",str(root/"check-critical-bodies.py")],check=True,stdout=subprocess.DEVNULL)
audit=json.loads((root/"source-availability.json").read_text())
assert audit["kani"]["pinned_upstream_source"]["commit"]=="53732d5e076329a62f71d3c6901886ce8a71e812"
assert audit["frozen_sbf"]["array_source"].startswith("not installed")
assert audit["frozen_aeneas_extraction"]["body_comparison"].startswith("The retained Aeneas extraction")
for p in root.rglob("*"):
    if not p.is_file() or p.name in {"SHA256SUMS","check_packet.py"}: continue
    assert p.suffix not in {".o",".a",".so",".dylib",".rlib",".rmeta",".olean",".olean.private",".olean.server"}, p
print("PASS: source hashes, three green Kani receipts, failed diagnostics, source/body pins, and source-only packet contents")
