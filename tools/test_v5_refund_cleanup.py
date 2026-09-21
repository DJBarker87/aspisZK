#!/usr/bin/env python3
"""Replay real archived refunds, then reject altered pins, roles and balances."""
import copy
import importlib.util
from pathlib import Path

path = Path(__file__).resolve().parents[1] / "release/aspis-v5-tag67-mainnet-rpc-archive-v1/verify.py"
spec = importlib.util.spec_from_file_location("rpc_archive", path)
archive = importlib.util.module_from_spec(spec)
spec.loader.exec_module(archive)
verify = archive.verify_refund_cleanup
captured = []


def capture(*args):
    verify(*args)
    captured.extend(args)


archive.verify_refund_cleanup = capture
archive.main()
decoded, binding, lifecycle = captured
for case in ("pin", "destination", "amount", "programdata", "proof", "fee"):
    rows = copy.deepcopy(decoded)
    evidence = copy.deepcopy(lifecycle)
    by_sig = {row["row"]["signature"]: row for row in rows}
    sweep = by_sig[binding["named_transactions"]["payer_sweep"]["signature"]]
    if case == "pin":
        evidence["identities"]["refund_pin_sha256"] = "0" * 64
    elif case == "destination":
        sweep["message"]["instructions"][0]["accounts"][1] = archive.SYSTEM_ID
    elif case == "amount":
        sweep["message"]["instructions"][0]["data"] = archive.struct.pack("<IQ", 2, 1)
    elif case in ("programdata", "proof"):
        name, key = (("programdata_close", "programdata") if case == "programdata"
                     else ("proof_close_tag64", "proof_account"))
        row = by_sig[binding["named_transactions"][name]["signature"]]
        index = row["message"]["keys"].index(evidence["identities"][key])
        row["result"]["meta"]["postBalances"][index] = 1
    else:
        sweep["result"]["meta"]["fee"] += 1
    try:
        verify(rows, binding, evidence)
    except SystemExit:
        continue
    raise AssertionError(f"accepted altered refund evidence: {case}")
print("PASS: six refund pin/role/amount/closure/fee rejection controls")
