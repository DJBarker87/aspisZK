#!/usr/bin/env python3
"""Apply explicit demo inputs only inside our isolated NUC source copy."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
assert str(ROOT) == "/home/dombarker/project-offloads/aspis-v8-devnet-smoke-20260909"
assert not (ROOT / ".git").exists()
ids = json.loads((HERE / "identities.json").read_text())["programs_and_accounts"]
alphabet = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
def key(s):
    n = 0
    for c in s:
        n = n * 58 + alphabet.index(c)
    b = n.to_bytes(32, "big")
    return "[" + ",".join(map(str, b)) + "]"
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

dispatch = ROOT / "programs/aspis-verifier/src/v7_pair_forest_dispatch.rs"
assert sha(dispatch) == "50ffb4598fca897e79bc7fca1fb4c1742c0ec15327032d117477e9a93150c4da"
source = dispatch.read_text()
for name, old, role in [
    ("POOL", "[0x41; 32]", "pool"),
    ("REGISTRY", "[0x44; 32]", "registry"),
]:
    before = f"const PAIR_FOREST_INVARIANT_{name}_PROGRAM_AUDIT_V1: [u8; 32] = {old};"
    assert source.count(before) == 1
    source = source.replace(before, before.replace(old, key(ids[role])))
dispatch.write_text(source)
lib = ROOT / "programs/aspis-verifier/src/lib.rs"
assert sha(lib) == "3905ac298f9f74602b6f8601e35d40dae30ae1aaa7592961253a167ac5117409"
lib.write_text(lib.read_text() + '\n#[cfg(v8_complete)]\n#[path="../../../docs/research/v8-isolated-devnet-smoke-20260909/proof_lifecycle.rs"]\npub mod v8_devnet_lifecycle;\n')
entry = ROOT / "docs/research/v8-no-work-100-20260907/experiments/complete-sbf/lib.rs"
assert sha(entry) == "5844e680601e17e9177afbee4a07301de2253c4ce6bcb0f93ff96dfaec669857"
entry.write_bytes((HERE / "verifier_entry.rs").read_bytes())
paths = [dispatch, lib, entry, HERE / "proof_lifecycle.rs", HERE / "identities.json"]
(HERE / "build-inputs.json").write_text(json.dumps({str(p.relative_to(ROOT)): sha(p) for p in paths}, indent=2) + "\n")
print("Fresh identity capability and existing lifecycle adapter installed; verification checks retained.")
