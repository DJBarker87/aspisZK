from pathlib import Path
import hashlib, json

ROOT = Path(__file__).resolve().parent
R = ROOT / "receipts"
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

result = json.loads((R / "gates/gate-result.json").read_text())
manifest = json.loads((R / "work/src/s9-candidate-source-manifest.json").read_text())
source_pins = json.loads((R / "source-pins/current-candidate-rust-cargo.json").read_text())
baseline_runs = R / "gates/baseline-runs.json"
baseline_b1 = R / "gates/baseline-cu.json"
assert sha(baseline_runs) == "a1b0a795f5101751950e42c7db19a1decfa3bd7f61d8ef37c85b211fa11a749f"
assert sha(baseline_b1) == "a86721fad52e8b16fe3b1e8f6061ac2b1a6923ec730d7f24d50c601d294a473d"
assert sha(R / "source-pins/current-candidate-rust-cargo.json") == "48af254839a777cbbb3080a538d3cd9e4af93be431f42fb1ee2c3cc8e1d04e4f"
assert manifest["files"]["crates/aspis-r1-cost-probe/src/weights.rs"] == "9338607afd636f43b3b830bbf9cf3cc0ced1fa7cc78b266282969e519577bccf"
assert sha(ROOT / "source/candidate-weights.rs") == manifest["files"]["crates/aspis-r1-cost-probe/src/weights.rs"]
assert result["research_head"] == "7998f6355d7163b5df1550f3440041b5b79dd48b"
artifact = "5aac14ef69f482c8b3bc95a400c321288b6a27f2b5b96adabcd21ad0c41019eb"
assert result["candidate_artifact_sha256"] == artifact
assert result["source_manifest_sha256"] == "48af254839a777cbbb3080a538d3cd9e4af93be431f42fb1ee2c3cc8e1d04e4f"

for phase in ("native", "sbf"):
    receipt = json.loads((R / f"gates/{phase}/receipt.json").read_text())
    assert receipt["exit_status"] == 0 and receipt["watchdog"] is None
    assert receipt["limits"] == {"memory.high": str(10 * 1024**3), "memory.max": str(12 * 1024**3), "memory.swap.max": "0"}
    assert receipt["scope_swap_current_bytes_at_exit"] == 0
    assert all(int(x.split()[1]) == 0 for x in receipt["memory_events_after"].splitlines())
assert json.loads((R / "gates/sbf/receipt.json").read_text())["candidate_artifact_sha256"] == artifact

rows = result["six_fixture_rows"]
assert len(rows) == 6
assert {x["fixture"] for x in rows} == {
    "transfer-13", "transfer-255", "transfer-1023",
    "withdrawal-13", "withdrawal-255", "withdrawal-1023"
}
assert result["all_six_approved_plus12000_pass"] is True
assert result["all_six_outputs_match"] is True
assert result["legacy_strict_b1_all_six_pass"] is False
assert result["legacy_prior_runner_all_six_pass"] is False
for row in rows:
    assert row["approved_plus12000_pass"] is True
    assert row["stage1_delta_cu"] <= 12000 and row["settlement_delta_cu"] <= 12000
    assert row["stage1_checkpoint_tail_same"] and row["return_data_same"]
    assert row["legacy_strict_b1_pass"] is False
    assert row["run_receipt"]["exit_status"] == 0 and not row["run_receipt"]["timed_out"]
    assert row["run_receipt"]["limits"] == {"memory.high": str(10 * 1024**3), "memory.max": str(12 * 1024**3), "memory.swap.max": "0"}
    cmd = json.loads((R / f"gates/fixtures/cu-{row['fixture']}/command.json").read_text())
    assert cmd["candidate_artifact_sha256"] == artifact
    assert cmd["input_artifact_and_proof_sha256"] == row["input_artifact_and_proof_sha256"]
    assert cmd["baseline_runs_sha256"] == sha(baseline_runs)
    assert cmd["b1_sha256"] == sha(baseline_b1)
    ev = R / f"runs/cu-{row['fixture']}/evidence.json"
    assert sha(ev) == row["candidate_evidence_sha256"]

stack = result["strict_stack_receipt"]
assert stack["exit_status"] == 0 and stack["candidate_artifact_sha256"] == artifact
assert stack["limits"] == {"memory.high": str(10 * 1024**3), "memory.max": str(12 * 1024**3), "memory.swap.max": "0"}
assert stack["linked_elf_sha256"] == "d7dd4d3b164cc0930c49c0b53fe5566f164713ed2aed40bee80c7692f9c8d9ab"
assert stack["stripped_so_sha256"] == artifact
assert stack["build_log_sha256"] == "9e0f20b7355a7e1c586ddcd38ad6bee97c89f59dd22cc6e1122b3b7d7bfe175e"
audit = json.loads((R / "gates/fixtures-stack-input/stack-audit.json").read_text())
assert audit["gate_pass"] is True and not audit["surviving_oversized"] and not audit["surviving_overwrites"]

binary_suffixes = {".so", ".elf", ".bin", ".o", ".rlib", ".a", ".dylib", ".dll", ".exe"}
found = [str(p.relative_to(ROOT)) for p in ROOT.rglob("*") if p.is_file() and p.suffix in binary_suffixes]
assert not found, f"binary payloads forbidden in this packet: {found}"
print("PASS: current-source native/SBF, six fixture, output identity, +12k, legacy B1, stack, and source-only checks")
