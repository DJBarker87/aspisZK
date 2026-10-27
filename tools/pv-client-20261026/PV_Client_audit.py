"""Read-only lexical route audit. No builds, keys, RPC or candidate execution."""
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
CANDIDATE = "1dfbd5711684d73fc2ff664cfae9ae78f7dd34f8"
BASE = "a0c5e1f66a9d16f76a22bd77fb0bc499a64a9978"
PLAN = "tools/r1-cost-probe/src/bin/devnet_spend/plan.rs"
CALLER = "crates/aspis-r1-cost-probe/src/RealR1_client.rs"
PROVER = "crates/aspis-r1-cost-probe/src/prover.rs"
ENTROPY = "crates/aspis-prover/src/state_only_entropy.rs"
PACKET = "docs/research/100bit-spend-path-20261013/evidence/client64-20261024/"


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT)


def candidate(path):
    # Other worktrees are never opened. Read candidate bytes via git show only.
    return git("show", f"{CANDIDATE}:{path}")


def pin(data):
    return {"sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}


paths = [
    PLAN, CALLER, PROVER, ENTROPY,
    "crates/aspis-r1-cost-probe/src/RealR1_client_tests.rs",
    "crates/aspis-r1-cost-probe/src/lib.rs", "crates/aspis-r1-cost-probe/Cargo.toml",
    "tools/r1-cost-probe/src/bin/devnet_spend.rs", "tools/r1-cost-probe/Cargo.toml",
    "tools/r1-cost-probe/Cargo.lock", "Cargo.toml", "Cargo.lock",
    "scripts/r1_devnet_spend.py", "scripts/r1_devnet_inventory.py",
    "scripts/r1_devnet_rpc.py", "xtask/src/main.rs", "xtask/src/v6_release.rs",
    "xtask/src/spend_devnet/v5.rs", "xtask/src/v5_cu_probe.rs",
    "tools/v7-live-pool-proof/src/lib.rs", "tools/v7-txv1-honest-proof/src/main.rs",
    "tools/v7-txv1-honest-proof/src/bin/build_proof_upload_requests.rs",
    "crates/aspis-pool-wallet-v1/src/live_pool_witness_adapter_v2.rs",
    "crates/aspis-prover/src/v7_pair_forest_fixture.rs",
    "crates/aspis-prover/src/state_only_spend.rs",
    "tools/r1-cost-probe/src/bin/pool_gate.rs",
    "tools/prover-speed-20261022/speed_profile.rs",
    "tools/v8-state-only-cu-probe/src/main.rs",
    "design/RELEASE-LEDGER-20261025.md",
    "docs/research/v8-r0-zk-20261009/r1p-final/REAL-R1-20261023.md",
    "docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployedReal.lean",
    "docs/research/100bit-spend-path-20261013/evidence/real-r1-20261023/summary.json",
]
for directory in ["crates/aspis-r1-cost-probe/examples", "crates/aspis-prover/examples"]:
    paths.extend(str(p.relative_to(ROOT)) for p in sorted((ROOT / directory).glob("*.rs")))
sources = {p: (ROOT / p).read_bytes() for p in paths}
# Require the inspected implementation to remain exactly at the audit baseline.
for p, data in sources.items():
    assert data == git("show", f"{BASE}:{p}"), f"source changed since baseline: {p}"

plan, caller, prover = [sources[p].decode() for p in [PLAN, CALLER, PROVER]]
assert "let result=prover::prove_masked_retrying(" in plan
assert "RealR1_client" not in plan and "generate_for_mask_nonce" not in plan
wrapper = prover.split("pub fn prove_masked_retrying(", 1)[1].split("\n}", 1)[0]
assert "StateOnlyAttemptSecrets::generate()" in wrapper
assert "StateOnlyAttemptSecrets::generate_for_mask_nonce(proof_account(k))" in caller
assert "prover::prove_masked_retrying_with(" in caller
assert 'ro(pk(q,"proof_account"))' in plan

# Recheck every source/dependency hash in the final historical Python receipt,
# without running the candidate's code or tests.
historical = json.loads(candidate(PACKET + "python-14.json"))
candidate_pins = {}
for p, expected in historical["source_and_dependency_hashes"].items():
    actual = pin(candidate(p))
    assert actual["sha256"] == expected, f"historical candidate hash mismatch: {p}"
    candidate_pins[p] = actual
cplan = candidate(PLAN).decode()
assert "RealR1_client::prove_for_proof_accounts(" in cplan
assert "prover::prove_masked_retrying(" not in cplan
assert "accounts.selected(result.attempts)?" in cplan
assert "accounts.publication(result.attempts," in cplan
for p in [CALLER, PROVER, ENTROPY]:
    assert candidate(p) == sources[p], f"candidate library dependency differs: {p}"
rust = json.loads(candidate(PACKET + "rust-03/receipt.json"))
for p, expected in rust["source_hashes"].items():
    assert pin(candidate(p.removeprefix("src/")))["sha256"] == expected

# Lexical evidence lines, deliberately not an absence/call-graph theorem.
terms = ("prove_masked", "generate_for_mask_nonce", "::generate()", "prove_for_proof_accounts")
lines = [{"path": p, "line": i, "text": line.strip()}
         for p, data in sources.items() if p.endswith(".rs")
         for i, line in enumerate(data.decode().splitlines(), 1)
         if any(t in line for t in terms)]
report = {
    "target": "PV_Client lexical route audit and historical candidate hash verification",
    "baseline_revision": BASE, "candidate_revision": CANDIDATE,
    "command": "python3 -B tools/pv-client-20261026/PV_Client_audit.py",
    "audit_script": pin(Path(__file__).read_bytes()),
    "exit": 0, "print_axioms": "N/A: source audit only",
    "current_source_pins": {p: pin(data) for p, data in sources.items()},
    "source_evidence_lines": lines, "candidate_pins": candidate_pins,
    "candidate_receipt_hashes_verified": len(candidate_pins),
    "checks": {"operational_planner_calls_generic96": True,
               "selected64_library_exists_but_not_called_by_planner": True,
               "candidate_planner_calls_selected64_without_generic_wrapper": True,
               "candidate_rust03_tested_sources_match": True},
    "result": "STOP: deployed selected64 integration requirement remains unmet",
    "limitations": ["No build, runtime proof, ELF acceptance or binary reachability check",
                    "Historical tests are reused descriptions, not rerun",
                    "No premise discharged; no source/refinement/privacy closure"],
    "budget": {"lean_attempts": 0, "kani_runs": 0, "cargo_commands": 0,
               "host_scopes": 0},
}
out = ROOT / "evidence/pv-client-20261026/source-audit.json"
out.parent.mkdir(parents=True, exist_ok=True)
out.write_text(json.dumps(report, indent=2) + "\n")
print(f"PASS: routing gap confirmed; {len(sources)} baseline source pins; "
      f"{len(candidate_pins)} historical candidate hashes verified; report={out.relative_to(ROOT)}")
