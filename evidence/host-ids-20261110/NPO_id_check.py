#!/usr/bin/env python3
"""NPO_: check the 10 November id map against the devnet recording (offline, read-only).
Usage: python3 -I NPO_id_check.py <NPC_TRANSACTIONS.json.xz> > NPO_ID_RECORDING_CHECK.json"""
import json, lzma, sys, base64, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from NPO_base58 import b58decode, b58encode
d = json.load(lzma.open(sys.argv[1]))
ids = {k: b58decode(v) for k, v in d["programs"].items()}
nov = {"verifier": "GqZzWuGTojfsxYnDzmyWKhdPGkce19xN1Txu9Vgnr5hy", "pool": "37hdATMkskKX1hiCWhz4nnzkD7GauYwX8EQwcpUDb3Zt",
       "registry": "9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q"}
out = {"recording_programs": d["programs"], "programs_match_NPO_DeployedIds_Nov": d["programs"] == nov, "steps": {}}
def acct_bytes(a):
    if "data_base64" in a: return base64.b64decode(a["data_base64"])
    v = a.get("data")
    if isinstance(v, list) and v and isinstance(v[0], str): return base64.b64decode(v[0])
    if isinstance(v, str):
        try: return bytes.fromhex(v)
        except ValueError: return base64.b64decode(v)
    if isinstance(v, dict) and "base64" in v: return base64.b64decode(v["base64"])
    return None
for t in d["transactions"]:
    if t["name"] not in ("transfer-stage1", "transfer-stage2"): continue
    rec = {"instructions_program": [], "accounts": {}}
    for ins in t["instructions"]:
        rec["instructions_program"].append(ins.get("program_id", ins.get("programId", ins.get("program"))))
    items = [(a["key"], a) for a in t["pre"]["accounts"]]
    for k, a in items:
        if not isinstance(a, dict): continue
        b = acct_bytes(a); owner = a.get("owner")
        hits = {}
        if b:
            for name, idb in ids.items():
                offs = [i for i in range(len(b) - 31) if b[i:i+32] == idb]
                if offs: hits[name] = offs
        rec["accounts"][k] = {"owner": owner, "len": len(b) if b else None, "id_offsets": hits}
    out["steps"][t["name"]] = rec
json.dump(out, sys.stdout, indent=1)
