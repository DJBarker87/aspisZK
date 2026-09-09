#!/usr/bin/env python3
"""Reconcile exact complete-transaction measurements; no CU extrapolation."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
E=ROOT/"evidence"/"complete"
VARIANTS={
 "typed_checked_pool":"complete-matrix-typed-v1",
 "hybrid_checked_pool":"complete-matrix-hybrid-v1",
 "hybrid_selected_pool":"complete-matrix-hybrid-selected-pool",
 "lazy_selected_pool":"complete-matrix-lazy-selected-pool",
 "partial_selected_pool":"complete-matrix-partial-selected-pool",
 "partial_max_body":"complete-matrix-partial-max",
 "selected_v7":"complete-matrix-v7-selected-pool",
}
def read(p):return json.loads(p.read_text())
def matrix(directory):
 rows={p.stem:read(p) for p in (E/directory).glob("*.json")}
 assert len(rows) in (16,24),(directory,len(rows))
 for name,x in rows.items():
  assert x["schema"]=="aspis.research.v8-v7.complete-comparison.v1"
  e,a=x["execution"],x["atomicity"]
  assert x["scenario"] in ("success","replay-nullifier","proof-rejection","wrong-release","stale-lane")
  expected=x["scenario"] in ("success","replay-nullifier")
  assert (e["outcome"]=="accepted")==expected
  assert e["simulation_equals_execution"] and not e["runtime_limit_is_diagnostic_override"]
  assert e["compute_units"]<=e["txv1_declared_compute_unit_limit"]<=1400000
  assert x["grinding_security_credit_bits"]==0
  for k in ("checkpoint_unchanged","entry_unchanged","master_unchanged","proof_unchanged","registry_unchanged"):
   assert a[k],(name,k)
  if expected:
   assert e["selected_verifier_cpi_observed_in_logs"] and e["return_data_bytes"]==792
   assert a["settled_history_equals_expected"] and a["settled_lane_equals_candidate"] and a["settled_marker_equals_expected"]
  else: assert a["failure_all_accounts_byte_exact"] and e["error"] is not None
  if x["scenario"]=="replay-nullifier":
   assert a["replay_preserved_settled_state_byte_exact"] and e["replay"]["error"] is not None
 out={}
 for op in ("transfer","withdrawal"):
  for count in (13,255):
   group=[x for name,x in sorted(rows.items()) if name.startswith(f"{op}-{count}-") and x["scenario"]=="success"]
   assert len(group) in (1,3)
   out[f"{op}-{count}"]=[{"cu":x["execution"]["compute_units"],
     "proof_bytes":x["fixture"]["proof_bytes"],"proof_sha256":x["fixture"]["proof_sha256"],
     "tx_bytes":x["execution"]["serialized_transaction_bytes"]} for x in group]
 return {"evidence_directory":str((E/directory).relative_to(ROOT)),"cases":len(rows),
  "artifacts":next(iter(rows.values()))["artifacts"],"shapes":out}
def stages(x):
 previous=1400000;name=None;out={}
 for line in x["execution"]["logs"]:
  if line.startswith("Program log: v8:"):name=line.removeprefix("Program log: ")
  m=re.fullmatch(r"Program consumption: (\d+) units remaining",line)
  if m and name:
   remaining=int(m[1]);out[name]=previous-remaining;previous=remaining;name=None
 out["after_last_checkpoint"]=x["execution"]["compute_units"]-(1400000-previous)
 assert sum(out.values())==x["execution"]["compute_units"]
 return out
def producer(directory):
 p=E/directory/"prover.log";s=p.read_text()
 events=[json.loads(line[5:]) for line in s.splitlines() if line.startswith("PERF ")]
 stress=[json.loads(line[7:]) for line in s.splitlines() if line.startswith("STRESS ")]
 times=[x["seconds"] for x in events if x.get("phase")=="prover_total_excludes_setup"]
 assert len(times)==3
 return {"evidence":str(p.relative_to(ROOT)),"seconds_excluding_setup":times,
  "mean_seconds_excluding_setup":sum(times)/len(times),
  "setup_seconds":next(x["seconds"] for x in events if x.get("phase")=="setup_compiler_encoder_matrix"),
  "peak_rss_kib":int(re.search(r"Maximum resident set size \(kbytes\): (\d+)",s)[1]),
  "swap":int(re.search(r"Swaps: (\d+)",s)[1]),
  "stress":stress,"p95_seconds":None,"p99_seconds":None}
v={key:matrix(directory) for key,directory in VARIANTS.items()}
for shape in v["partial_selected_pool"]["shapes"]:
 old=v["lazy_selected_pool"]["shapes"][shape];new=v["partial_selected_pool"]["shapes"][shape]
 assert [x["proof_sha256"] for x in old]==[x["proof_sha256"] for x in new]
 assert [a["cu"]-b["cu"] for a,b in zip(old,new)]==[26488]*3
 assert all(x["proof_bytes"]==40282 for x in v["partial_max_body"]["shapes"][shape])
 # Pool / Registry artifacts are identical in final V7 / V8 comparison.
for role in ("pool","registry"):
 assert len({v[k]["artifacts"][role]["sha256"] for k in ("selected_v7","partial_selected_pool","partial_max_body")})==1
cap=list((E/"complete-cap1200-partial-max").glob("*.json"))
assert len(cap)==6
for p in cap:
 x=read(p);assert x["execution"]["outcome"]=="accepted"
 assert x["execution"]["txv1_declared_compute_unit_limit"]==1200000
 assert x["fixture"]["proof_bytes"]==40282
rollback=list((E/"complete-rollback-partial").glob("*.json"));assert len(rollback)==2
for p in rollback:
 x=read(p);assert x["execution"]["outcome"]=="rejected"
 assert x["atomicity"]["failure_all_accounts_byte_exact"]
 assert x["execution"]["selected_verifier_cpi_observed_in_logs"]
best=v["partial_max_body"]["shapes"]
out={"schema":"aspis.v8.complete-performance.v1",
 "base_revision":"8fba5920852911f5666a0982ecc5dd9f0048b18b","variants":v,
 "profiled_lazy_stages":{p.stem:stages(read(p)) for p in sorted((E/"complete-profile-v1").glob("*.json"))},
 "wire":{"canonical_fixed_fields":697,"fixed_field_bytes":16,"roots_bytes":52,"nonces_bytes":24,
  "queries":22,"record_bytes":621,"frontier_each":296,"digest_bytes":26,
  "maximum_body_bytes":697*16+52+24+22*621+2*296*26,"candidate_afterstate_bytes":688,
  "proof_account_header_bytes":40,"asq8_instruction_bytes":320,"asf8_statement_bytes":1880,"asr8_result_bytes":792},
 "provers":{directory:producer(directory) for directory in
  ["complete-partial-prover-v1"]+[f"complete-max-{op}-{count}-v1" for op in ("transfer","withdrawal") for count in (13,255)]},
 "worst_observed_max_body_cu":max(x["cu"] for rows in best.values() for x in rows),
 "full_transaction_no_regression":False,"all_shapes_below_1200000":False,
 "actual_1200000_limit_passes":len(cap),"withdrawal_post_verifier_atomic_rollbacks":len(rollback),
 "full_security_bits":None,"grinding_security_credit_bits":0,
 "security_obligations":{"global_accepted_recovery_failure":"unbounded",
  "full_view_zk":"unresolved","resource_bounded_fs":"unresolved",
  "translated_source_acceptance_equivalence":"unresolved"},
 "v7_comparison_limitations":["one frozen strict proof per shape, not the same query schedule",
  "same SBF v1.54/compiler, LiteSVM/runtime, accounts, selected Pool/Registry and accounting",
  "V7 uses original workspace release profile/lock; V8 standalone fat-LTO/codegen1/overflow-checks=true profile/lock",
  "not a release certificate, universal maximum-CU bound or deployment-feature availability claim"]}
assert out["wire"]["maximum_body_bytes"]==40282
print(json.dumps(out,indent=2))
