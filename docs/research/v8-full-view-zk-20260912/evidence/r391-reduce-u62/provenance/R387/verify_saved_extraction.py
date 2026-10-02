#!/usr/bin/env python3
"""Verify saved R387 receipt, exact source hashes, and emitted structural rows; never launches tools."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
result=json.loads((ROOT/"result.json").read_text())
accept=json.loads((ROOT/"acceptance.json").read_text())
cmd=json.loads((ROOT/"extract-command.json").read_text())
artifact=json.loads((ROOT/"R387ReduceU62.llbc").read_text())
tr=artifact["translated"]
assert result["charon_exit_status"]==0 and artifact["has_errors"] is False
assert result["llbc_sha256"]==sha(ROOT/"R387ReduceU62.llbc")=="fdb448185f0f077cf0df303709da52a8be05eeb800767a4ea9a03f7f3c71afc4"
assert accept["accepted_for_further_review"] and accept["root_candidate_counts"]=={"reduce_u62":1}
assert accept["external_structured_roots"]==[{"def_id":0,"name_tail":"reduce_u62","source_line":103,"local":False,"body_kind":"Structured"}]
assert cmd["start_from"]==["aspis_core::field::M31::reduce_u62"] and cmd["monomorphize"] is False
assert cmd["rustflags_sha256"]=="f2485133cd857d119d387fcdda1a7fe2607e04dbec4756adbaacd3e765363613"
assert cmd["verified_source_hashes"]["aspis_core_field.rs"]=="639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499"
assert cmd["source_revision_recorded"]=="a962b9ac222caa6d2f715882240b9b9856158261"
assert [(f["def_id"],f["item_meta"]["name"][-1]["Ident"][0]) for f in tr["fun_decls"] if f]==[(0,"reduce_u62"),(1,"reduce_u64"),(2,"P")]
assert len(tr["type_decls"])==1 and tr["type_decls"][0]["def_id"]==0
assert len(tr["global_decls"])==1 and tr["global_decls"][0]["def_id"]==0
assert tr["ordered_decls"]==[]
rows=json.loads((ROOT/"selected-transitive-declarations.json").read_text())
assert rows["artifact_sha256"]==result["llbc_sha256"] and len(rows["fun_decls"])==3
metrics=json.loads((ROOT/"extraction-metrics.json").read_text())
assert metrics["gnu_time_max_rss_kib"]=="Maximum resident set size (kbytes): 611960" and metrics["swap_count"].strip()=="Swaps: 0"
assert metrics["caps"]=={"MemoryHigh":"5G","MemoryMax":"7G","MemorySwapMax":"0","TasksMax":128}
print(json.dumps({"status":"PASS","llbc_sha256":result["llbc_sha256"],"root_and_helper_ids":[0,1],"ordered_decls":0,"translation":"not run"},indent=2))
