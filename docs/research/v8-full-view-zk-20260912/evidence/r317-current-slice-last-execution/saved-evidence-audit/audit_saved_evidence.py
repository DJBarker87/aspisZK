#!/usr/bin/env python3
"""Read-only consistency audit of published R316/R317 evidence."""
from __future__ import annotations
import hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
DOCS=ROOT/"docs/research/v8-full-view-zk-20260912"
CONFIG={
 "R316":{"slug":"r316-current-slice-last-raw","target":DOCS/"lean/AspisR316SliceLastRaw.lean","names":["AspisR316SliceLastRaw.core.slice.Slice.last"],"metrics":("0:01.00",2526400,0,0)},
 "R317":{"slug":"r317-current-slice-last-execution","target":DOCS/"lean/AspisV8R19/R317SliceLastExecution.lean","names":["AspisV8R19.R317SliceLastExecution.last_complete","AspisV8R19.R317SliceLastExecution.last_none_iff"],"metrics":("0:01.15",2533560,0,0)},
}
FOUNDATIONS={"propext","Classical.choice","Quot.sound"}
AX_RE=re.compile(r"^'([^']+)' depends on axioms: \[(.*?)\]",re.M|re.S)
def sha(b): return hashlib.sha256(b).hexdigest()
def amap(s): return {n:tuple(v.strip() for v in ax.replace("\n"," ").split(",")) for n,ax in AX_RE.findall(s)}
result={"audit":"read-only saved evidence audit; no compilation or tracked edits","bundles":{},"findings":[]}
for name,c in CONFIG.items():
 d=DOCS/"evidence"/c["slug"]; m=json.loads((d/"manifest.json").read_text()); sums=json.loads((d/"SHA256SUMS.json").read_text())
 bad=[]; missing=[]
 for rel,want in sums.items():
  p=d/rel
  if not p.is_file(): missing.append(rel)
  elif sha(p.read_bytes())!=want: bad.append(rel)
 allfiles={str(p.relative_to(d)) for p in d.rglob("*") if p.is_file() and p.name!="SHA256SUMS.json"}
 unlisted=sorted(allfiles-set(sums)); copy=d/"source"/c["target"].name; log=(d/m["log"]).read_text()
 tm=re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)",log); rss=re.search(r"Maximum resident set size \(kbytes\): (\d+)",log); sw=re.search(r"Swaps: (\d+)",log); ex=re.search(r"Exit status: (\d+)",log)
 metrics=(tm.group(1),int(rss.group(1)),int(sw.group(1)),int(ex.group(1)))
 logax=amap(log); fileax=amap((d/"axioms.txt").read_text()); expected=set(c["names"])
 r={"outer_manifest_entries":len(sums),"bad_or_missing_hashes":bad+missing,"unlisted_files":unlisted,
 "target_sha256":sha(c["target"].read_bytes()),"manifest_sha256":m["source_sha256"],"source_copy_sha256":sha(copy.read_bytes()),
 "target_and_copy_match":c["target"].read_bytes()==copy.read_bytes() and sha(c["target"].read_bytes())==m["source_sha256"],
 "metrics_log_wall_rss_swaps_exit":list(metrics),"metrics_manifest_wall_rss_swaps_exit":[m["wall_time"],m["peak_rss_kib"],m["swaps"],m["exit_status"]],"metrics_match":metrics==c["metrics"]==(m["wall_time"],m["peak_rss_kib"],m["swaps"],m["exit_status"]),
 "source_revision":m["source_revision"],"source_revision_exists":subprocess.run(["git","cat-file","-e",m["source_revision"]+"^{commit}"],cwd=ROOT,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode==0,
 "resources":m["resources"],"runner_has_expected_limits":all(x in (d/"run_focus.py").read_text() for x in ["MemoryHigh=5G","MemoryMax=7G","MemorySwapMax=0","TasksMax=128"]),
 "axiom_reports":len(fileax),"axiom_names_match":set(fileax)==expected==set(logax),"axiom_file_matches_log":fileax==logax,
 "axioms_are_subset_of_foundations":bool(fileax) and all(set(v)<=FOUNDATIONS for v in fileax.values()),"axioms_have_no_sorryAx":"sorryAx" not in (d/"axioms.txt").read_text(),"success_log":"Finished with result: success" in log}
 result["bundles"][name]=r
 for k in ["bad_or_missing_hashes","unlisted_files"]:
  if r[k]:result["findings"].append(f"{name}: {k}={r[k]}")
 for k in ["target_and_copy_match","metrics_match","source_revision_exists","runner_has_expected_limits","axiom_names_match","axiom_file_matches_log","axioms_are_subset_of_foundations","axioms_have_no_sorryAx","success_log"]:
  if not r[k]:result["findings"].append(f"{name}: {k} failed")

# Check preflight library source SHA records against their copies.
pre=DOCS/"evidence/r317-current-slice-last-execution/library-source-preflight"
prehash=json.loads((pre/"source-hashes.json").read_text())
prechecks={rel:(pre/rel).is_file() and sha((pre/rel).read_bytes())==expected for rel,expected in prehash.items()}
result["R317_library_source_copies"]={"count":len(prechecks),"all_match":all(prechecks.values()),"checks":prechecks}
if not all(prechecks.values()):result["findings"].append("R317 library preflight source hash mismatch")

raw=(DOCS/"lean/AspisR316SliceLastRaw.lean").read_text(); proof=(DOCS/"lean/AspisV8R19/R317SliceLastExecution.lean").read_text()
last_stmt=re.search(r"theorem last_complete\s*(.*?)\s*:= by",proof,re.S)
result["R316_R317_boundary"]={
 "R316_single_explicit_sub_adapter":raw.count("UScalar.sub") == 1 and raw.count("Usize.sub")==0,
 "R316_body_guard_length_reads_sub_index_option":all(x in raw for x in ["let i := Slice.len self","if i >= 1#usize","let i1 := Slice.len self","let i2 ← UScalar.sub i1 1#usize","Slice.index_usize self i2","ok (some last)","ok none"]),
 "R317_generic_over_all_types_and_slices":bool(last_stmt) and "{T : Type} (xs : Slice T)" in last_stmt.group(1),
 "R317_no_external_premise_in_last_complete_signature":bool(last_stmt) and "(h" not in last_stmt.group(1),
 "R317_concludes_success_option_getLast":bool(last_stmt) and ".ok xs.val.getLast?" in last_stmt.group(1),
 "R317_empty_and_nonempty_cases_derived_internally":"by_cases h : 1 ≤ xs.length" in proof and "List.length_eq_zero_iff" in proof and "List.getLast?_eq_getElem?" in proof,
 "no_generic_panic_or_out_of_bounds_equivalence_claim":"OPanic" not in proof and "OUBequivalence" not in proof,
 "no_verified_compiler_or_whole_batch_claim":"not a verified Rust compiler theorem or complete batch/freeze correspondence" in (DOCS/"R317_CURRENT_SLICE_LAST_EXECUTION.md").read_text(),
 "security_boundary_open":"soundness remain open" in (DOCS/"R317_CURRENT_SLICE_LAST_EXECUTION.md").read_text(),
}
if not all(result["R316_R317_boundary"].values()):result["findings"].append("R316/R317 source or boundary check failed")

r316d=DOCS/"evidence/r316-current-slice-last-raw/raw-adapter-audit/rejected-old-subtraction-api"
r317d=DOCS/"evidence/r317-current-slice-last-execution/development-history/rejected"
result["rejected_history"]={
 "R316_old_subtraction_scaffold_present":all((r316d/x).is_file() for x in ["AspisR316SliceLastRaw.lean","aspis-focus-1790923285872763000.log","reason.json"]),
 "R316_reason_is_only_api_name_adapter": "Usize.sub" in (r316d/"reason.json").read_text() and "UScalar.sub" in (r316d/"reason.json").read_text(),
 "R317_premature_draft_present":(r317d/"premature-dependent-draft.lean").is_file(),
 "R317_failed_proof_draft_present":(r317d/"draft-1790923519583102000.lean").is_file(),
 "R317_rejected_logs_present":len(list(r317d.glob("*.log")))==2,
 "R317_rejection_reason_present":(r317d/"reason.json").is_file(),
}
if not all(result["rejected_history"].values()):result["findings"].append("Rejected staging/proof history incomplete")
# The R316 first-remaining statement is from before R317.
r316note=(DOCS/"R316_CURRENT_SLICE_LAST_RAW.md").read_text(); r317note=(DOCS/"R317_CURRENT_SLICE_LAST_EXECUTION.md").read_text()
result["progress_note"]={"R316_frontier_predates_R317": "Prove the emitted result for every valid slice" in r316note and "For every valid Slice T, the emitted actual Slice.last body returns exactly" in r317note,
 "R317_frontier_names_actual_prefix_loops": "Bind and prove both actual forward prefix loops" in r317note}
if result["progress_note"]["R316_frontier_predates_R317"]:
 result["findings"].append("R316 note first_remaining_proposition still requests universal Slice.last proof, completed by R317; stale progress metadata only.")
binding=json.loads((DOCS/"evidence/r316-current-slice-last-raw/raw-adapter-audit/binding-audit.json").read_text())
result["R316_binding_audit_annotation"]={"precompile_boundary_text":binding["boundary"],"stale_uncompiled_annotation": "Uncompiled" in binding["boundary"] and result["bundles"]["R316"]["metrics_match"]}
if result["R316_binding_audit_annotation"]["stale_uncompiled_annotation"]:
 result["findings"].append("Copied R316 binding-audit.json still labels the raw staging 'Uncompiled' although the published R316 target and matching success log show compilation; historical staging annotation only.")
result["overall"]="PASS_WITH_TWO_STALE_R316_ANNOTATIONS" if len(result["findings"])==2 and all(x.startswith("R316 note") or x.startswith("Copied R316 binding-audit") for x in result["findings"]) else ("PASS" if not result["findings"] else "FINDINGS")
Path(__file__).resolve().parent.joinpath("audit.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
