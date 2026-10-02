#!/usr/bin/env python3
"""Read-only audit of published R318 raw prefix-loop evidence."""
from __future__ import annotations
import hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
DOCS=ROOT/"docs/research/v8-full-view-zk-20260912"
D=DOCS/"evidence/r318-current-batch-prefix-raw"
TARGET=DOCS/"lean/AspisR318BatchPrefixRaw.lean"
FOUNDATIONS={"propext","Classical.choice","Quot.sound"}
AX_RE=re.compile(r"^'([^']+)' depends on axioms: \[(.*?)\]",re.M|re.S)
def sha(b):return hashlib.sha256(b).hexdigest()
def axmap(s):return {n:tuple(v.strip() for v in ax.replace("\n"," ").split(",")) for n,ax in AX_RE.findall(s)}
m=json.loads((D/"manifest.json").read_text()); sums=json.loads((D/"SHA256SUMS.json").read_text())
bad=[];missing=[]
for rel,want in sums.items():
 p=D/rel
 if not p.is_file():missing.append(rel)
 elif sha(p.read_bytes())!=want:bad.append(rel)
files={str(p.relative_to(D)) for p in D.rglob("*") if p.is_file() and p.name!="SHA256SUMS.json"}
unlisted=sorted(files-set(sums)); source=D/"source/AspisR318BatchPrefixRaw.lean"; target=TARGET.read_bytes();log=(D/m["log"]).read_text()
tm=re.search(r"Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)",log);rss=re.search(r"Maximum resident set size \(kbytes\): (\d+)",log);sw=re.search(r"Swaps: (\d+)",log);ex=re.search(r"Exit status: (\d+)",log)
metrics=(tm.group(1),int(rss.group(1)),int(sw.group(1)),int(ex.group(1)))
logax=axmap(log);fileax=axmap((D/"axioms.txt").read_text())
expected={"AspisR318BatchPrefixRaw.circle_norm.joined_inverse.line_norm.r110_norm."+n for n in ["batch_loop0.body","batch_loop0","batch_loop1.body","batch_loop1"]}
result={"audit":"read-only saved evidence audit; no compilation or tracked edits","outer_manifest":{"entries":len(sums),"bad_or_missing_hashes":bad+missing,"unlisted_files":unlisted},
 "target":{"path":str(TARGET.relative_to(ROOT)),"sha256":sha(target),"manifest_sha256":m["source_sha256"],"evidence_source_sha256":sha(source.read_bytes()),"target_matches_manifest_and_copy":target==source.read_bytes() and sha(target)==m["source_sha256"]},
 "execution":{"metrics_log_wall_rss_kib_swaps_exit":list(metrics),"metrics_manifest_wall_rss_kib_swaps_exit":[m["wall_time"],m["peak_rss_kib"],m["swaps"],m["exit_status"]],"metrics_match":metrics==(m["wall_time"],m["peak_rss_kib"],m["swaps"],m["exit_status"]),"source_revision":m["source_revision"],"source_revision_exists":subprocess.run(["git","cat-file","-e",m["source_revision"]+"^{commit}"],cwd=ROOT,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode==0,"resources":m["resources"],"runner_caps_match":all(x in (D/"run_focus.py").read_text() for x in ["MemoryHigh=5G","MemoryMax=7G","MemorySwapMax=0","TasksMax=128"]),"success_log":"Finished with result: success" in log},
 "axioms":{"report_count":len(fileax),"names_match_expected":set(fileax)==expected==set(logax),"report_file_matches_log":fileax==logax,"all_foundational_only":bool(fileax) and all(set(v)<=FOUNDATIONS for v in fileax.values()),"sorryAx_absent":"sorryAx" not in (D/"axioms.txt").read_text()},
}
# Independently extract the four generated declaration blocks from saved R292 source and compare exact bytes.
source_input=ROOT/".r21-scratch/r292-private-batch-translation/generated/AspisR292PrivateBatch/Funs.lean"
source_text=source_input.read_text();target_text=target.decode()
names=["circle_norm.joined_inverse.line_norm.r110_norm.batch_loop0.body","circle_norm.joined_inverse.line_norm.r110_norm.batch_loop0","circle_norm.joined_inverse.line_norm.r110_norm.batch_loop1.body","circle_norm.joined_inverse.line_norm.r110_norm.batch_loop1"]
blocks={}
for n in names:
 hits=list(re.finditer(r"(?m)^def "+re.escape(n)+r"(?:\s|$)",source_text))
 if len(hits)!=1:blocks[n]=False;continue
 pos=hits[0].start(); st=source_text.rfind("/--",0,pos); end=source_text.find("/--",pos)
 if end<0:end=len(source_text)
 b=source_text[st:end].rstrip("\n")
 blocks[n]=target_text.count(b)==1
result["generated_blocks"]={"source_file_sha256":sha(source_input.read_bytes()),"four_exact_blocks_match":all(blocks.values()),"blocks":blocks,"only_direct_external_template":"core.slice.Slice.last","template_inventory_is_direct_only":json.loads((D/"dependency-inventory/verification.json").read_text())["semantic_boundary"]=="direct syntactic dependency inventory only"}
# Distinguish final harmless wrapper from body identity, while exposing stale copied audit data.
rawaudit=D/"raw-adapter-audit"; rawfile=(rawaudit/"AspisR318BatchPrefixRaw.lean").read_bytes(); binding=json.loads((rawaudit/"binding-audit.json").read_text())
without=rawfile.replace(b"\nnoncomputable section\n",b"\n",1)
inner={}
for line in (rawaudit/"SHA256SUMS").read_text().splitlines():
 h,rel=line.split("  ",1); p=rawaudit/rel
 inner[rel]={"listed_sha256":h,"actual_sha256":sha(p.read_bytes()) if p.is_file() else None,"matches":p.is_file() and sha(p.read_bytes())==h}
result["wrapper_and_builder"]={"final_wrapper_count":target_text.count("noncomputable section"),"builder_template_has_noncomputable_section":"noncomputable section" in (rawaudit/"build_raw.py").read_text(),"removing_wrapper_reproduces_precompile_audit_sha":sha(without)==binding["target_sha256"],"final_file_hash":sha(rawfile),"precompile_binding_audit_target_hash":binding["target_sha256"],"precompile_compiled_flag":binding["compiled"],"inner_sum_entries":inner,"inner_sum_all_match":all(x["matches"] for x in inner.values()),"only_wrapper_delta":sha(without)==binding["target_sha256"] and all(blocks.values())}
result["scope"]={"prefix_and_loop_execution_not_proved_by_R318":True,"manifest_first_remaining":m["first_remaining_proposition"],"note_keeps_batch_caller_open":"complete batch caller are not proved" in m["proved_boundary"],"library_correspondence_open":"independent Rust correspondence" in m["proved_boundary"],"security_not_claimed":"soundness remain open" in (DOCS/"R318_CURRENT_BATCH_PREFIX_RAW.md").read_text()}
result["findings"]=[]
for label,ok in [("outer manifest hashes",not bad and not missing and not unlisted),("target identity",result["target"]["target_matches_manifest_and_copy"]),("metrics",result["execution"]["metrics_match"] and result["execution"]["source_revision_exists"] and result["execution"]["runner_caps_match"] and result["execution"]["success_log"]),("axioms",result["axioms"]["names_match_expected"] and result["axioms"]["report_file_matches_log"] and result["axioms"]["all_foundational_only"] and result["axioms"]["sorryAx_absent"]),("exact generated blocks",all(blocks.values()))]:
 if not ok:result["findings"].append(label+" failed")
if not result["wrapper_and_builder"]["inner_sum_all_match"]:result["findings"].append("Raw-adapter nested SHA256SUMS target entry is stale: recorded pre-wrapper hash does not match final target.")
if binding["compiled"] is False:result["findings"].append("Copied raw binding audit retains precompile compiled=false status despite published successful R318 compile.")
result["overall"]="PASS_WITH_STALE_PRECOMPILE_AUDIT_METADATA" if len(result["findings"])==2 and all(x.startswith("Raw-adapter nested") or x.startswith("Copied raw binding") for x in result["findings"]) else ("PASS" if not result["findings"] else "FINDINGS")
Path(__file__).resolve().parent.joinpath("audit.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
