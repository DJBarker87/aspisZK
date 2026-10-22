#!/usr/bin/env python3
from pathlib import Path
import hashlib, json

p = Path(__file__).parent
sha = lambda q: hashlib.sha256(q.read_bytes()).hexdigest()
source = p / "sources/S4Tx1ActualGammaBridgeV1.lean"
receipt = json.loads((p / "receipt/receipt.json").read_text())
preflight = json.loads((p / "receipt/preflight.json").read_text())
command = json.loads((p / "receipt/command.json").read_text())
assert receipt["exit_status"] == 0 and receipt["watchdog_abort"] is None
assert receipt["process_swaps"] == 0
assert receipt["source_sha256"] == sha(source)
assert receipt["object_sha256"] == "e2e418926603375cd9c1da479e09ff2094ecac2faac6f9e6ab8933e293e62d2d"
assert preflight["closure_preflight"]["missing"] == []
assert preflight["closure_preflight"]["modules"] == 7609
assert command["argv"][-1].endswith("/S4Tx1ActualGammaBridgeV1.lean")
assert "-j1" in command["argv"] and "4400" in command["argv"]
assert "S4Tx1InstalledPrepareBridgeV1" in (p / "receipt/direct-import-pins.json").read_text()
axioms = (p / "receipt/axioms.txt").read_text()
assert "sorryAx" not in axioms
assert all(x in axioms for x in ("propext", "Classical.choice", "Quot.sound"))
assert not list((p / "receipt").glob("*.olean"))
for line in (p / "SHA256SUMS").read_text().splitlines():
    expected, rel = line.split("  ", 1)
    assert sha(p / rel) == expected, f"checksum mismatch: {rel}"
print("PASS")
