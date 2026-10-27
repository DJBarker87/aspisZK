#!/usr/bin/env python3
"""Validate retained proof receipts and restored checked source snapshots."""
from pathlib import Path
import hashlib, json, re

ROOT = Path(__file__).resolve().parents[2]
E = Path(__file__).resolve().parent
receipts = [json.loads(p.read_text()) for p in sorted(E.glob("F3X_???/receipt.json"))]
assert len(receipts) == 66
limits = {"memory.high":"6442450944", "memory.max":"8589934592", "memory.swap.max":"0", "pids.max":"64"}
assert all(r["limits"] == limits and r["swaps"] == "0" for r in receipts)
manifest, theorems = {}, {}
for p in sorted((ROOT/"lean").glob("F3X_*.lean")):
    sha = hashlib.sha256(p.read_bytes()).hexdigest()
    matches = [r for r in receipts if r["exit_status"] == 0 and
               int(r["attempt"].split("_")[1]) <= 47 and r["source_hashes"].get(p.name) == sha]
    assert matches, p
    chosen = matches[-1]
    manifest[p.name] = dict(sha256=sha, successful_attempt=chosen["attempt"], deps_fingerprint=chosen["deps_fingerprint"])
    source = p.read_text()
    namespace = re.search(r"namespace (AspisR1\.F3X_\w+)",source)
    for name in re.findall(r"^theorem\s+(\w+)",source,re.M):
        full = namespace.group(1)+"."+name
        assert "#print axioms "+name in source or "#print axioms "+full in source, full
        log = (E/chosen["attempt"]/"stdout.log").read_text()
        found = re.search(rf"'{re.escape(full)}' depends on axioms:\s*\[([^]]*)\]",log)
        if found:
            axioms = [a.strip() for a in found.group(1).split(",") if a.strip()]
        else:
            assert "'"+full+"' does not depend on any axioms" in log, full
            axioms = []
        assert set(axioms) <= {"propext","Classical.choice","Quot.sound"}, full
        theorems[full] = dict(receipt=chosen["attempt"], axioms=axioms)
(E/"F3X_source-manifest.json").write_text(json.dumps(manifest,indent=2)+"\n")
(E/"F3X_theorems.json").write_text(json.dumps(theorems,indent=2)+"\n")
(E/"F3X_attempts.jsonl").write_text("".join(json.dumps(r)+"\n" for r in receipts))
final = dict(source_checkpoint="7840756da4",actual_compiles=len(receipts),
    passing_attempts=sum(r["exit_status"]==0 for r in receipts), failed_attempts=sum(r["exit_status"]!=0 for r in receipts),
    kani=0,delivered_modules=len(manifest),delivered_top_theorems=len(theorems),
    max_peak_rss_kib=max(int(r["peak_rss_kib"]) for r in receipts),all_swaps_zero=True,unused_budget=34,
    stopping_reason="Local launcher configuration write ENOSPC; local-lean rule5 requires stop and lead infrastructure repair",
    pending_last_attempt="F3X_066 Nonvacuity projection failure against old headline; excluded",
    current_host_cache="Contains interim F3X objects after047. MUST NOT be treated as a coherent delivered-source closure. Recompile own prefix after lead infrastructure fix. Historical coherent receipts035/046/047 and exact source/dependency fingerprints are retained.")
(E/"F3X_FINAL.json").write_text(json.dumps(final,indent=2)+"\n")
print(json.dumps(final,indent=2))
