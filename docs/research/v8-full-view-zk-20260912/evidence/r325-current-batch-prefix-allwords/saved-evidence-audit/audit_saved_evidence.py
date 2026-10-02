#!/usr/bin/env python3
"""Read-only audit of promoted R324/R325 saved evidence."""
from __future__ import annotations
import hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
DOCS=ROOT/"docs/research/v8-full-view-zk-20260912"
CFG={
 "R324":{"slug":"r324-current-batch-prefix-complete","target":DOCS/"lean/AspisV8R19/R324BatchPrefixComplete.lean","names":["batch_loop0_complete","batch_loop1_complete"],"metrics":("0:01.61",3716960,0,0)},
 "R325":{"slug":"r325-current-batch-prefix-allwords","target":DOCS/"lean/AspisV8R19/R325BatchPrefixAllWords.lean","names":["sourceWord_read","batch_loop0_all_words","batch_loop1_all_words"],"metrics":("0:01.59",3711012,0,0)},
}
FOUNDATIONS={"propext","Classical.choice","Quot.sound"}
AX_RE=re.compile(r"^'([^']+)' depends on axioms: \[(.*?)\]",re.M|re.S)
def sha(b):return hashlib.sha256(b).hexdigest()
def axmap(s):return {n:tuple(x.strip() for x in body.replace("\n"," ").split(",")) for n,body in AX_RE.findall(s)}
result={"audit":"read-only saved evidence; no Lean compilation or tracked edits","bundles":{},"findings":[]}
for name,c in CFG.items():
 d=DOCS/"evidence"/c["slug"];m=json.loads((d/"manifest.json").read_text());sums=json.loads((d/"SHA256SUMS.json").read_text())
 bad=[];missing=[]
 for rel,want in sums.items():
  p=d/rel
  if not p.is_file():missing.append(rel)
  elif sha(p.read_bytes())!=want:bad.append(rel)
 allf={str(p.relative_to(d)) for p in d.rglob("*") if p.is_file() and p.name!="SHA256SUMS.json"};unlisted=sorted(allf-set(sums))
 src=d/"source"/c["target"].name;log=(d/m["log"]).read_text()
 t=re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)",log);r=re.search(r"Maximum resident set size \(kbytes\): (\d+)",log);s=re.search(r"Swaps: (\d+)",log);e=re.search(r"Exit status: (\d+)",log)
 metrics=(t.group(1),int(r.group(1)),int(s.group(1)),int(e.group(1)))
 logax=axmap(log);fileax=axmap((d/"axioms.txt").read_text())
 ns="AspisV8R19.R324BatchPrefixComplete" if name=="R324" else "AspisV8R19.R325BatchPrefixAllWords"
 expected={ns+"."+x for x in c["names"]}
 rec={"manifest_entries":len(sums),"hash_problems":bad+missing,"unlisted_files":unlisted,"target_sha256":sha(c["target"].read_bytes()),"manifest_sha256":m["source_sha256"],"source_copy_sha256":sha(src.read_bytes()),"target_copy_match":src.read_bytes()==c["target"].read_bytes() and sha(src.read_bytes())==m["source_sha256"],"metrics_log_wall_rss_kib_swaps_exit":list(metrics),"metrics_manifest_wall_rss_kib_swaps_exit":[m["wall_time"],m["peak_rss_kib"],m["swaps"],m["exit_status"]],"metrics_match":metrics==c["metrics"]==(m["wall_time"],m["peak_rss_kib"],m["swaps"],m["exit_status"]),"source_revision":m["source_revision"],"source_revision_exists":subprocess.run(["git","cat-file","-e",m["source_revision"]+"^{commit}"],cwd=ROOT,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode==0,"resources":m["resources"],"runner_caps_match":all(x in (d/"run_focus.py").read_text() for x in ["MemoryHigh=5G","MemoryMax=7G","MemorySwapMax=0","TasksMax=128"]),"axiom_count":len(fileax),"axiom_names_match":set(fileax)==expected==set(logax),"axioms_file_matches_log":fileax==logax,"axioms_foundational_only":bool(fileax) and all(set(v)<=FOUNDATIONS for v in fileax.values()),"sorryAx_absent":"sorryAx" not in (d/"axioms.txt").read_text(),"success_log":"Finished with result: success" in log}
 result["bundles"][name]=rec
 for k in ["hash_problems","unlisted_files"]:
  if rec[k]:result["findings"].append(f"{name}: {k}={rec[k]}")
 for k in ["target_copy_match","metrics_match","source_revision_exists","runner_caps_match","axiom_names_match","axioms_file_matches_log","axioms_foundational_only","sorryAx_absent","success_log"]:
  if not rec[k]:result["findings"].append(f"{name}: {k} failed")

r324=(DOCS/"lean/AspisV8R19/R324BatchPrefixComplete.lean").read_text();r325=(DOCS/"lean/AspisV8R19/R325BatchPrefixAllWords.lean").read_text();m325=json.loads((DOCS/"evidence/r325-current-batch-prefix-allwords/manifest.json").read_text())
sig324=re.search(r"theorem batch_loop0_complete\s*(.*?)\s*:= by",r324,re.S)
prefix_result=re.search(r"def prefixResult\s*(.*?)\s*theorem batch_loop0_complete",r324,re.S)
checks={
 "R324_exact_remaining_count_premise":"hremaining : iter.i + n = iter.slice.val.length" in r324,
 "R324_exact_raw_source_read_premise":"hread : ∀ j, iter.i ≤ j → j < iter.slice.val.length" in r324 and "some (f j)" in r324,
 "R324_no_canonical_capacity_success_nonzero_premise":bool(sig324) and all(x not in sig324.group(1) for x in ["canonical", "hcap", "nonzero", "success"]),
 "R325_universal_iterator_and_vec_statement":"theorem batch_loop0_all_words (iter : PrefixIter) (px : alloc.vec.Vec U32)" in r325,
 "R325_no_external_premises":"batch_loop0_all_words (iter : PrefixIter) (px : alloc.vec.Vec U32) :" in r325,
 "R325_total_sourceWord_default_and_read_lemma":"xs.val[j]?.getD 0#u32" in r325 and "theorem sourceWord_read" in r325,
 "R325_default_proved_unreachable_for_active_reads":"sourceWord_read iter.slice j hj" in r325,
 "R324_recurrence_zero_and_successor_clauses":bool(prefix_result) and "| _, 0, px => .ok px" in prefix_result.group(1) and "| i, n + 1, px => do" in prefix_result.group(1),
 "R325_no_success_nonzero_canonical_or_capacity_premise":all(x not in r325 for x in ["hsuccess", "hcap", "nonzero", "Canonical"]),
 "caller_and_Rust_correspondence_open":"not independent Rust/compiler correspondence or a full batch proof" in m325["proved_boundary"] and "actual batch guard/initialization" in m325["first_remaining_proposition"],
 "batch_and_security_open":all(x in m325["first_remaining_proposition"] for x in ["actual batch guard/initialization", "callback chronology", "soundness"]),
}
result["theorem_scope"]=checks
if not all(checks.values()):result["findings"].append("Theorem premise/scope boundary check failed")
result["overall"]="PASS" if not result["findings"] else "FINDINGS"
Path(__file__).resolve().parent.joinpath("audit.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
