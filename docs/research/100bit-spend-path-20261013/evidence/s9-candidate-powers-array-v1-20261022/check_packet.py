#!/usr/bin/env python3
import hashlib, json, pathlib, sys
root = pathlib.Path(__file__).resolve().parent
src = root / "sources/S9CandidateExplicitPowersArrayBridgeV1.lean"
receipt = json.loads((root / "receipts/receipt.json").read_text())
preflight = json.loads((root / "receipts/preflight.json").read_text())
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(src) == receipt["source_sha256"] == preflight["source_sha256"]
assert receipt["exit_status"] == 0 and receipt["process_swaps"] == 0
assert receipt["object_sha256"] == "97cf3423dc52566dc2ced7abde02d20af8bb290e3b5b8421d5147b3a28867d27"
assert "candidate_explicit_powers4_matches_p6" in src.read_text()
assert "hmul4" in src.read_text()
assert not list(root.rglob("*.olean"))
print("S9 candidate powers array source-only packet: PASS")
