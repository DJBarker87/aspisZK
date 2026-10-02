#!/usr/bin/env python3
"""Read-only audit of published R319/R321 saved successes."""
from __future__ import annotations
import hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
DOCS=ROOT/"docs/research/v8-full-view-zk-20260912"
CFG={
 "R319":{"slug":"r319-current-batch-prefix-step-execution","target":DOCS/"lean/AspisV8R19/R319BatchPrefixStepExecution.lean","names":["next_done","next_step","body0_done","body0_active","body0_empty_prefix","body0_step","body1_eq_body0"],"metrics":("0:01.64",3709456,0,0)},
 "R321":{"slug":"r321-current-batch-prefix-loop-execution","target":DOCS/"lean/AspisV8R19/R321BatchPrefixLoopExecution.lean","names":["prefixValues_length","batch_loop0_prefixValues","batch_loop1_eq_loop0"],"metrics":("0:01.69",3716704,0,0)},
}
FOUNDATIONS={"propext","Classical.choice","Quot.sound"}
AX_RE=re.compile(r"^'([^']+)' depends on axioms: \[(.*?)\]",re.M|re.S)
def sha(b):return hashlib.sha256(b).hexdigest()
def axmap(s):return {n:tuple(x.strip() for x in body.replace("\n"," ").split(",")) for n,body in AX_RE.findall(s)}
result={"audit":"read-only saved evidence; no Lean compilation or tracked edits","bundles":{},"findings":[]}
for name,c in CFG.items():
 d=DOCS/"evidence"/c["slug"]; m=json.loads((d/"manifest.json").read_text()); sums=json.loads((d/"SHA256SUMS.json").read_text())
 bad=[];missing=[]
 for rel,want in sums.items():
  p=d/rel
  if not p.is_file():missing.append(rel)
  elif sha(p.read_bytes())!=want:bad.append(rel)
 allf={str(p.relative_to(d)) for p in d.rglob("*") if p.is_file() and p.name!="SHA256SUMS.json"};unlisted=sorted(allf-set(sums))
 src=d/"source"/c["target"].name; log=(d/m["log"]).read_text()
 t=re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)",log); r=re.search(r"Maximum resident set size \(kbytes\): (\d+)",log); s=re.search(r"Swaps: (\d+)",log); e=re.search(r"Exit status: (\d+)",log)
 metrics=(t.group(1),int(r.group(1)),int(s.group(1)),int(e.group(1)))
 logax=axmap(log);fileax=axmap((d/"axioms.txt").read_text());expected={f"AspisV8R19.{name}{'BatchPrefixStepExecution' if name=='R319' else 'BatchPrefixLoopExecution'}.{x}" for x in c["names"]}
 # Correct fully-qualified namespaces are R319BatchPrefixStepExecution/R321BatchPrefixLoopExecution.
 expected={f"AspisV8R19.{('R319BatchPrefixStepExecution' if name=='R319' else 'R321BatchPrefixLoopExecution')}.{x}" for x in c["names"]}
 rec={"manifest_entries":len(sums),"hash_problems":bad+missing,"unlisted_files":unlisted,"target_sha256":sha(c["target"].read_bytes()),"manifest_sha256":m["source_sha256"],"source_copy_sha256":sha(src.read_bytes()),"target_copy_match":src.read_bytes()==c["target"].read_bytes() and sha(src.read_bytes())==m["source_sha256"],"metrics_log_wall_rss_kib_swap_exit":list(metrics),"metrics_manifest_wall_rss_kib_swap_exit":[m["wall_time"],m["peak_rss_kib"],m["swaps"],m["exit_status"]],"metrics_match":metrics==c["metrics"]==(m["wall_time"],m["peak_rss_kib"],m["swaps"],m["exit_status"]),"source_revision":m["source_revision"],"source_revision_exists":subprocess.run(["git","cat-file","-e",m["source_revision"]+"^{commit}"],cwd=ROOT,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode==0,"resources":m["resources"],"runner_caps_match":all(x in (d/"run_focus.py").read_text() for x in ["MemoryHigh=5G","MemoryMax=7G","MemorySwapMax=0","TasksMax=128"]),"axiom_count":len(fileax),"axiom_names_match":set(fileax)==expected==set(logax),"axioms_file_matches_log":fileax==logax,"axioms_foundational_only":bool(fileax) and all(set(v)<=FOUNDATIONS for v in fileax.values()),"sorryAx_absent":"sorryAx" not in (d/"axioms.txt").read_text(),"success_log":"Finished with result: success" in log}
 result["bundles"][name]=rec
 for k in ["hash_problems","unlisted_files"]:
  if rec[k]:result["findings"].append(f"{name}: {k}={rec[k]}")
 for k in ["target_copy_match","metrics_match","source_revision_exists","runner_caps_match","axiom_names_match","axioms_file_matches_log","axioms_foundational_only","sorryAx_absent","success_log"]:
  if not rec[k]:result["findings"].append(f"{name}: {k} failed")

r319=(DOCS/"lean/AspisV8R19/R319BatchPrefixStepExecution.lean").read_text();r321=(DOCS/"lean/AspisV8R19/R321BatchPrefixLoopExecution.lean").read_text();m321=json.loads((DOCS/"evidence/r321-current-batch-prefix-loop-execution/manifest.json").read_text())
prems={"remaining_count":"hremaining : iter.i + n = iter.slice.val.length" in r321,"canonical_remaining_reads":"hx : ∀ j, iter.i ≤ j → j < iter.slice.val.length" in r321 and "some (encodeBase (f j))" in r321,"encoded_last_value":"hlast : px.val.getLast? = some (encodeBase p)" in r321,"capacity":"hcap : px.val.length + n ≤ Usize.max" in r321,"no_nonzero_or_success_assumption":"nonzero" not in r321 and "success" not in r321,"zero_iterations_present":"| _, 0, _ => []" in r321 and "| zero =>" in r321,"correct_prefixValues_clauses":"| _, 0, _ => []" in r321 and "| i, n + 1, p =>" in r321,"caller_premises_remain_open":"complete source caller" in m321["proved_boundary"],"rust_correspondence_remains_open":"independent Rust-library/compiler correspondence are not proved" in m321["proved_boundary"]}
result["R321_theorem_premises_and_boundary"]=prems
if not all(prems.values()):result["findings"].append("R321 premise/order/boundary check failed")
# Ensure final target does not claim caller closure or security.
notes={"R319_caller_and_std_correspondence_open":"caller invariants remain open" in (DOCS/"R319_CURRENT_BATCH_PREFIX_STEP_EXECUTION.md").read_text() and "independent Rust-library correspondence" in (DOCS/"R319_CURRENT_BATCH_PREFIX_STEP_EXECUTION.md").read_text(),"R321_batch_source_security_open":all(x in (DOCS/"R321_CURRENT_BATCH_PREFIX_LOOP_EXECUTION.md").read_text() for x in ["complete source caller","independent Rust-library/compiler correspondence","soundness remain open"])}
result["scope_notes"]=notes
if not all(notes.values()):result["findings"].append("Scope note overstates boundary")
result["overall"]="PASS" if not result["findings"] else "FINDINGS"
Path(__file__).resolve().parent.joinpath("audit.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
