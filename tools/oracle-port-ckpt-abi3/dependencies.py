#!/usr/bin/env python3
"""Read-only source/driver and concurrent S10 dependency inventory."""
from pathlib import Path
import hashlib,json,subprocess
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/ckpt-abi3-20261021'
def git(*args):return subprocess.check_output(['git',*args],cwd=R,text=True).strip()
def source(path,start,end):
 p=R/path;s=p.read_text();a=s.index(start);b=s.index(end,a)
 return dict(path=path,source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),first_line=s[:a].count('\n')+1,last_line=s[:b].count('\n')+1,excerpt_sha256=hashlib.sha256(s[a:b].encode()).hexdigest())
research=git('rev-parse','research')
report_path='docs/research/100bit-spend-path-20261013/design/S10-INVENTORY-20261021.md'
s10=git('log',research,'-1','--format=%H','--',report_path)
landed=subprocess.run(['git','merge-base','--is-ancestor',s10,research],cwd=R).returncode==0
files=git('ls-tree','-r','--name-only',research).splitlines()
report=git('show',research+':'+report_path)
imported=[report_path,'docs/research/100bit-spend-path-20261013/lean/OraclePortS10ModelInventory.lean']
for path in imported:
 assert (R/path).read_bytes()==subprocess.check_output(['git','show',research+':'+path],cwd=R)
assert 'checkpoint resume and Pool' in report and 'not source call sites' in report
result=dict(schema='checkpoint-driver-obligation-inventory-v1',source_revision=git('rev-parse','HEAD'),research_revision=research,s10_revision=s10,s10_tip_on_research=landed,s10_report=dict(path=report_path,sha256=hashlib.sha256((report+'\n').encode()).hexdigest(),imported=True,imported_paths=imported,reason='landed model-stage module and report imported byte-identically; worker explicitly leaves frozen source tree and checkpoint source Site open'),research_s10_lean_paths=[p for p in files if 'S10' in p and p.endswith('.lean')],caller_spans=[source('crates/aspis-r1-cost-probe/src/candidate.rs','pub fn tx1<','\n#[inline(never)]\nfn tx2_common'),source('crates/aspis-r1-cost-probe/src/candidate.rs','fn tx2_common<','\n/// Stage 2 with checkpoint provenance')],obligations=[
 dict(id='section-adoption',status='open',exact='Instantiate atomic semantic states and local source/model equalities in OraclePortCkptAbi3Sections.fixed_composition; identify the emitted full resume caller with that nine-section composition, including Box/allocation/errors.'),
 dict(id='kernel-byte-identification',status='open',exact='Relate OraclePortCkptAbi2Extracted.body_byte and decoder word contracts to OraclePortCheckpointAbiC5.encode/decode via explicit U32-to-exact-field and U8-to-Byte maps; use canonicality from successful strict reads where appropriate, and prove all 18 blocks/fields, not only word quotient preservation.'),
 dict(id='rust-reached-state',status='open',exact='For the parsed p,q,i produced by OraclePortCkptAbi2Reached.accepted_inputs, identify Rust prepare Context and fields with C5.prepared; identify Accumulator::new/query_loop(0..10)/pending.finish with C3.write(model i.data rho q), all 64 weights, rhs, power, next, and both retained proof/public slices.'),
 dict(id='physical-allocation-iteration',status='open',exact='Adopt shared/mutable reader/writer iteration and fallible heap::filled try_reserve_exact/resize, plus Vec capacity and Box::new, at the source/std translation boundary; owned std iterator content is proved but physical allocation/Drop is not represented.'),
 dict(id='tx1-tx2-driver-join',status='open',exact='Construct source checkpoint Site/Signature/arguments and source tree for tx1 and tx2_common, preserving all six ordered digest reads and source rejection timing; prove both source/model caller identities and enrichment stability required by AcceptedRunJoin. Existing checkpointThen_not_erased forbids simply deleting the six reads.'),
 dict(id='runtime',status='separate',exact='P2/P2-prime same-snapshot/carrier binding remains independent and unchanged.')],complete_checkpoint_cone=False,accepted_run_join=False)
(E/'driver-obligations.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['research_revision','s10_revision','s10_tip_on_research','research_s10_lean_paths','accepted_run_join']}))
