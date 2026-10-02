#!/usr/bin/env python3
"""Read-only consistency audit of published R311 and R313 evidence."""
from __future__ import annotations
import hashlib, json, re, subprocess
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
DOCS = ROOT / "docs/research/v8-full-view-zk-20260912"
CONFIG = {
 "R311": {
  "slug":"r311-current-batch-reverse-loop-execution",
  "target":DOCS/"lean/AspisV8R19/R311BatchReverseLoopExecution.lean",
  "axioms":["setNat_eq_vec_set","setNat_length","batch_loop2_reverseModel","batch_loop3_body_eq_loop2_body","batch_loop3_eq_batch_loop2"],
  "metrics":("0:01.75",3724832,0,0),
 },
 "R313": {
  "slug":"r313-current-batch-reverse-index-errors",
  "target":DOCS/"lean/AspisV8R19/R313BatchReverseIndexErrors.lean",
  "axioms":["prefix_index_error","output_index_error","input_index_error"],
  "metrics":("0:01.51",3710172,0,0),
 },
}
FOUNDATIONS={"propext","Classical.choice","Quot.sound"}
AX_RE=re.compile(r"^'([^']+)' depends on axioms: \[(.*?)\]",re.M|re.S)
def sha(b): return hashlib.sha256(b).hexdigest()
def amap(s): return {n:tuple(t.strip() for t in ax.replace("\n"," ").split(",")) for n,ax in AX_RE.findall(s)}
result={"audit":"read-only saved evidence; no Lean compilation", "bundles":{},"findings":[]}
for name,cfg in CONFIG.items():
 d=DOCS/"evidence"/cfg["slug"]
 m=json.loads((d/"manifest.json").read_text()); sums=json.loads((d/"SHA256SUMS.json").read_text())
 bad=[]; missing=[]
 for rel,want in sums.items():
  p=d/rel
  if not p.is_file(): missing.append(rel)
  elif sha(p.read_bytes())!=want: bad.append(rel)
 allfiles={str(p.relative_to(d)) for p in d.rglob("*") if p.is_file() and p.name!="SHA256SUMS.json"}
 unlisted=sorted(allfiles-set(sums))
 source=d/"source"/cfg["target"].name
 log=(d/m["log"]).read_text()
 tt=re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)",log)
 rss=re.search(r"Maximum resident set size \(kbytes\): (\d+)",log)
 sw=re.search(r"Swaps: (\d+)",log)
 ex=re.search(r"Exit status: (\d+)",log)
 met=(tt.group(1),int(rss.group(1)),int(sw.group(1)),int(ex.group(1)))
 logax=amap(log); fileax=amap((d/"axioms.txt").read_text())
 expected={f"AspisV8R19.R311BatchReverseLoopExecution.{x}" for x in cfg["axioms"]} if name=="R311" else {f"AspisV8R19.R313BatchReverseIndexErrors.{x}" for x in cfg["axioms"]}
 r={
  "outer_sha256_entries":len(sums),"bad_or_missing_hashes":bad+missing,"unlisted_files":unlisted,
  "target_sha256":sha(cfg["target"].read_bytes()),"manifest_sha256":m["source_sha256"],"source_copy_sha256":sha(source.read_bytes()),
  "target_matches_manifest_and_copy":sha(cfg["target"].read_bytes())==m["source_sha256"]==sha(source.read_bytes()) and source.read_bytes()==cfg["target"].read_bytes(),
  "metrics_log_wall_rss_swaps_exit":list(met),"metrics_manifest_wall_rss_swaps_exit":[m["wall_time"],m["peak_rss_kib"],m["swaps"],m["exit_status"]],
  "metrics_match":met==cfg["metrics"]==(m["wall_time"],m["peak_rss_kib"],m["swaps"],m["exit_status"]),
  "source_revision":m["source_revision"],"source_revision_exists":subprocess.run(["git","cat-file","-e",m["source_revision"]+"^{commit}"],cwd=ROOT,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode==0,
  "resources":m["resources"],"runner_has_caps":all(x in (d/"run_focus.py").read_text() for x in ["MemoryHigh=5G","MemoryMax=7G","MemorySwapMax=0","TasksMax=128"]),
  "log_reports":len(logax),"expected_axiom_names":sorted(expected),"axiom_names_match":set(fileax)==expected and set(logax)==expected,
  "axiom_file_matches_log":fileax==logax,"all_reports_foundations_only":all(set(v)<=FOUNDATIONS for v in fileax.values()) and all(fileax.values()),
  "no_sorryAx_in_success_report":"sorryAx" not in (d/"axioms.txt").read_text(),"successful_log":"Finished with result: success" in log,
 }
 result["bundles"][name]=r
 for k in ["bad_or_missing_hashes","unlisted_files"]:
  if r[k]: result["findings"].append(f"{name}: {k}={r[k]}")
 for k in ["target_matches_manifest_and_copy","metrics_match","source_revision_exists","runner_has_caps","axiom_names_match","axiom_file_matches_log","all_reports_foundations_only","no_sorryAx_in_success_report","successful_log"]:
  if not r[k]: result["findings"].append(f"{name}: {k} failed")

r311note=(DOCS/"R311_CURRENT_BATCH_REVERSE_LOOP_EXECUTION.md").read_text()
r313note=(DOCS/"R313_CURRENT_BATCH_REVERSE_INDEX_ERRORS.md").read_text()
r311src=CONFIG["R311"]["target"].read_text()
r313src=CONFIG["R313"]["target"].read_text()
review=json.loads((DOCS/"evidence/r311-current-batch-reverse-loop-execution/lead-review.json").read_text())
result["R311_boundary"]={
 "has_start_one_end_n_plus_one": "hstart : iter.iter.start.val = 1" in r311src and "hend : iter.iter.end.val = n + 1" in r311src,
 "selected_reads_and_output_bound_are_explicit": "hxs : ∀ j" in r311src and "hpx : ∀ j" in r311src and "hlen : n < ox.length" in r311src,
 "actual_loop_unfolded_by_proof": "loop.eq_def" in r311src,
 "model_update_bridge_is_proved": "setNat_eq_vec_set" in r311src and "setNat_length" in r311src,
 "zero_allowed_and_caller_premises_unjustified": review["zero_allowed"] and not review["premises_justified_for_actual_caller"],
 "source_std_correspondence_and_security_open": not review["pinned_standard_library_source_correspondence_closed"] and not review["whole_batch_or_privacy_or_soundness_claim"],
}
result["R313_boundary"]={
 "error_order_explicit": all(x in r313src for x in ["prefix_index_error","output_index_error","input_index_error"]),
 "later_error_canonical_operands_explicit": "R250PrivateBaseExecution.mul_encoded" in r313src,
 "caller_and_whole_source_library_correspondence_open": "does not prove caller index invariants or whole batch/source-library correspondence" in (DOCS/"R313_CURRENT_BATCH_REVERSE_INDEX_ERRORS.md").read_text(),
 "published_first_remaining_is_stale_after_R311": "Prove complete reverse-loop termination and its output under explicit local invariants" in r313note and "terminates and returns exactly the finite mathematical reverse recurrence" in r311note,
}
if not all(result["R311_boundary"].values()): result["findings"].append("R311 boundary or premise report inconsistent")
if not all(result["R313_boundary"].values()): result["findings"].append("R313 boundary report check failed")
result["findings"].append("R313 note first_remaining_proposition predates R311 and still asks to prove complete reverse-loop termination/output under local invariants, which R311 now supplies; this is stale progress metadata, not a R313 proof/log mismatch.")

r311d=DOCS/"evidence/r311-current-batch-reverse-loop-execution/development-history/rejected"
result["R311_rejected_history"]={
 "rejected_draft_count":len(list(r311d.glob("draft-*.lean"))),
 "rejected_log_count":len(list(r311d.glob("*.log"))),
 "rejected_log_has_compile_errors":"error:" in next(r311d.glob("*.log")).read_text(),
 "unverified_worker_draft_retained":(DOCS/"evidence/r311-current-batch-reverse-loop-execution/development-history/unverified-worker-draft.lean").is_file(),
}
result["overall"]="PASS_WITH_STALE_R313_FRONTIER_NOTE" if len(result["findings"])==1 and result["findings"][0].startswith("R313 note first_remaining_proposition") else ("PASS" if not result["findings"] else "FINDINGS")
Path(__file__).resolve().parent.joinpath("audit.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
