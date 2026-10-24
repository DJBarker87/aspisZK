#!/usr/bin/env python3
"""Audit same-call semantic source installation through owned stage1/writer."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=load(E/'s1-semantic-targets.json');a=load(E/'accepted-targets.json')['targets'];pins=load(E/'s1-semantic-import-pins.json');wall=0.;rss=0;reports=0
for target,attempt in m['targets'].items():
 p=S/(target+'.lean');r=load(E/attempt/'receipt.json')
 assert r['exit_status']==0 and r['swaps']==0 and r['print_axioms'],target
 assert a[target]['receipt']==attempt+'/receipt.json'
 assert sha(p)==sha(E/attempt/'source.lean')==r['source_sha256']==pins['targets'][target]['source_sha256']
 assert r['object_sha256']==pins['targets'][target]['object_sha256']
 assert '-j1' in r['command'] and '-M4400' in r['command']
 assert not re.search(r'\b(sorry|native_decide|bv_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text(),re.M)
 for x in r['print_axioms']:
  if 'does not depend on any axioms' not in x:
   ax=re.search(r'depends on axioms:\s*\[([^]]*)\]',x,re.S)
   assert ax and set(re.findall(r'[A-Za-z_.]+',ax[1]))<={'propext','Classical.choice','Quot.sound'},(target,x)
  reports+=1
 wall+=r['wall_seconds'];rss=max(rss,r['peak_rss_bytes'])
 for f in (E/attempt).rglob('*'):
  if f.is_file():assert f.suffix not in ['.olean','.llbc','.rlib','.rmeta','.o','.a','.so','.dylib']
for path,h in load(E/'s1-semantic-source-pins.json')['sources'].items():assert sha(R/path)==h,path
for path,h in load(E/'s1-semantic-tool-pins.json')['scripts'].items():assert sha(R/path)==h,path
for row in load(E/'s1-semantic-reused-source-pins.json')['sources']:assert sha(R/row['source'])==row['sha256']
import subprocess,sys
subprocess.run([sys.executable,str(R/'tools/s1-semantic-port-20261024/check-models.py'),'--check-source'],check=True)
carrier=(S/'S1SemanticCarrierV1.lean').read_text()
for field in ['roots','challenges','alpha','claims','extra','before_z1','state_before_z0','z','transcript']:assert field+':=' in carrier
assert 'semanticEquiv' in carrier and 'wire_error_round' in carrier and 'wire_error_back' in carrier
leaf=(S/'S1SemanticInstallationV1.lean').read_text()
assert 'VerifyPrefix.verify' in leaf and 'FinishModel.finish R' in leaf and 'currentSem sem' in leaf
assert 'some observe => ops.op9 D pub bytes hash (some observe)' in leaf
owned=(S/'S1OwnedStage1SemanticRootsV1.lean').read_text()
assert 'S6CurrentStage1FirstJoin.accepted_stage1' in owned and 'first_current_prepared_new' in owned
assert 'verify_roots' in owned and 'verify_alpha' in owned and 'originalNew' in owned
assert 'prepared.semantic_alpha' in owned and 'Tx1Reachability.afterPrepare' in owned
writer=(S/'S1TopWriterSemanticV1.lean').read_text()
assert 'Port4A_PrepareCut.returned' in writer and 'prepare_semantic_roots' in writer
for premise in ['(hsem :','(hnew :','(roots :','(canonical :','(first :']:assert premise not in owned and premise not in writer
for gate in ['source_semantic_body_installed','source_semantic_root_calls_derived','semantic_alpha_canonical','enclosing_owned_stage1_same_statement_semantic_roots_alpha','enclosing_writer_semantic_roots_alpha']:assert m[gate]
for gate in ['whole_s1_closed','whole_s6_closed','native_sdk_binding','full_prepared_binding','physical_compact_buffer_binding','all_semantic_leaves_installed']:assert not m[gate]
print(json.dumps(dict(targets=len(m['targets']),wall_seconds=wall,peak_rss_bytes=rss,swaps=0,standard_or_empty_axiom_reports=reports,whole_s1_closed=False,whole_s6_closed=False)))
