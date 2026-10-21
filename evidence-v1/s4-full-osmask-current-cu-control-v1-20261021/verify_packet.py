#!/usr/bin/env python3
"""Offline consistency checks for the retained full-OS-mask CU evidence."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda p: json.loads((ROOT / p).read_text())

prov = load("provenance/original-corpus-provenance.json")
row = prov["inventory_row"]
origin = load("provenance/original-run-evidence.json")
assert row["label"] == "var-transfer-s10-genesis-p0-fresh-0"
assert row["source_mask_mode"] == "os" and row["measured_proof_identical"] is True
assert row["proof_sha256"] == "42fc1617dbc212ef07f7a5cd4f177d2014530198a2fefa40d25914d79ca46ee8"
assert row["public_sha256"] == "5b3b4ea275b0f447bdfc69a726b6e42f20d40c54af414feb1832a6a4174c9410"
assert row["proof_bytes"] == 57607
assert origin["fixture"]["mask_entropy_option"] == "os"
assert origin["fixture"]["mask_mode"] == "full-mask"
assert origin["fixture"]["entropy_source"] == "OS getrandom via StateOnlyAttemptSecrets::generate"
assert origin["fixture"]["proof_byte_mutated_by_harness"] is False
assert origin["fixture"]["proof_sha256"] == origin["fixture"]["submitted_proof_sha256"] == row["proof_sha256"]
assert origin["execution"]["outcome"] == "accepted"
assert sha(ROOT / "provenance/corpus_inventory.py") == prov["inventory_generator_sha256"]
assert sha(ROOT / "provenance/original-run-evidence.json") == prov["original_run_evidence_sha256"]

cfg = load("source/config.json")
assert cfg["proof_sha256"] == row["proof_sha256"]
assert cfg["public_sha256"] == row["public_sha256"]
assert cfg["baseline_elf_sha256"] == "dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34"
assert cfg["candidate_elf_sha256"] == "40dc75742430dd198bd51d519aa5a41bad4a45e8f173ccbd51c6d5be344ac3f0"
assert cfg["pool_elf_sha256"] == "121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548"
assert cfg["registry_elf_sha256"] == "7ad46f0d4b102a7c9699149d23bf6e065b6151feeaca95977d0a3146167d01ab"
assert sha(ROOT / "source/pool_gate.rs") == cfg["pool_gate_source_sha256"]
assert sha(ROOT / "source/Cargo.toml") == "e797c3e47c9e058c4a9a9356241b1f044484114f9a03f0b1fd45f42cf5be04a0"
assert sha(ROOT / "source/Cargo.lock") == "8b4eeda2858edbb6963b50782643bf27fc3299549b2e00521e581566e7f8e409"
source = (ROOT / "source/pool_gate.rs").read_text()
for flag in ('"--seed"', '"--uniform-lane"', '"--zeroed-genesis-page"'):
    assert flag in source
build = load("build/receipt.json")
assert build["exit_status"] == 0
assert build["binary_sha256"] == "cfc19b39b5ebfb28bc6f97467eb525f31a40e370cfa067a078dda79f90b26142"
assert build["limits"] == {"memory.high":"805306368","memory.max":"1073741824","memory.swap.max":"0"}
assert build["swap_current_bytes"] == 0

expected = {
    "default": {"elf": cfg["baseline_elf_sha256"], "stage1": 1196068, "settlement": 1139924, "nested": 1042510},
    "candidate": {"elf": cfg["candidate_elf_sha256"], "stage1": 1206885, "settlement": 1150423, "nested": 1053009},
}
run_values = {}
for label, want in expected.items():
    r = load(f"measure/{label}/result.json")
    ev = r["gate_evidence"]
    ex = ev["execution"]
    assert r["runner_receipt"]["exit_status"] == 0
    assert ex["error"] is None and ex["outcome"] == "accepted"
    assert r["elf_sha256"] == want["elf"]
    assert r["proof_sha256"] == row["proof_sha256"] and r["public_sha256"] == row["public_sha256"]
    assert r["proof_bytes"] == row["proof_bytes"]
    # Reused fixtures do not carry entropy provenance forward; only original corpus evidence does.
    assert ev["fixture"]["kind"] == "explicit-reuse"
    assert ev["fixture"]["mask_mode"] == "unknown-from-reused-proof"
    assert ex["stage1_compute_units"] == want["stage1"]
    assert ex["compute_units"] == want["settlement"]
    nested = [int(m.group(1)) for line in ex["logs"] if (m := re.search(r"Program 7Q2\S* consumed (\d+) of", line))]
    assert nested == [want["nested"]], nested
    assert want["stage1"] < ex["declared_compute_unit_limit"]
    assert want["settlement"] < ex["declared_compute_unit_limit"]
    assert r["runner_receipt"]["limits"] == {"memory.high":"536870912","memory.max":"1073741824","memory.swap.max":"0"}
    assert r["runner_receipt"]["swap_current_bytes"] == 0
    run_values[label] = (ex["stage1_compute_units"], ex["compute_units"], nested[0])
assert run_values["candidate"][0] - run_values["default"][0] == 10817
assert run_values["candidate"][1] - run_values["default"][1] == 10499
assert run_values["candidate"][2] - run_values["default"][2] == 10499

bad = load("diagnostics/current-invalid-pool-gate/measurement.json")
assert bad["verifier_completed"] is False
assert bad["execution"]["error"] == "InstructionError(2, InvalidInstructionData)"
assert bad["execution"]["cu"] == 1052
assert "Error: wrong frozen proof" in (ROOT / "diagnostics/old-wire-r18/stderr.log").read_text()
assert "reused proof public statement differs" in (ROOT / "diagnostics/adopt-poolgate-mismatch/output.log").read_text()
assert "failed to parse manifest" in (ROOT / "diagnostics/build-manifest-failure/output.log").read_text()

for p in ROOT.rglob("*"):
    if p.is_file():
        assert p.suffix.lower() not in {".bin", ".so", ".o", ".a", ".rlib"}, p
        assert "keypair" not in p.name.lower(), p
sumfile = ROOT / "SHA256SUMS"
if sumfile.exists():
    for line in sumfile.read_text().splitlines():
        expected_sha, rel = line.split("  ", 1)
        assert sha(ROOT / rel) == expected_sha, rel
print("PASS: original full-mask provenance, exact source/artifact pins, stage1/settlement/nested CU, diagnostics, and source-only/key-exclusion checks")
