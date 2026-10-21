#!/usr/bin/env python3
"""Validate the focused proof packet and publish an honest partial certificate."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s8-kani-20261021'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for script in ['generate.py','prepare-lean.py','contract-kit/generate.py']:
 subprocess.run([sys.executable,str(Path(__file__).parent/script),'--check'],check=True)
proofs=[json.loads(p.read_text())|{'receipt_path':str(p.relative_to(E))} for p in sorted((E/'proofs').glob('*/receipt.json'))]
host=[json.loads(p.read_text())|{'receipt_path':str(p.relative_to(E))} for p in sorted((E/'receipts').glob('*/receipt.json'))]
accepted={}
for r in proofs:
 p=B/'lean'/(r['module'].replace('.','/')+'.lean')
 if r['exit_status']==0 and p.exists() and sha(p)==r['source_sha256']:
  for line in r['print_axioms']:
   assert not any(x in line for x in ['sorryAx','Lean.ofReduceBool','trustMe']),line
   m=re.search(r'depends on axioms:\s*\[([^]]*)\]',line,re.S)
   if m:assert set(re.findall(r'[A-Za-z_.]+',m[1]))<=set(['propext','Classical.choice','Quot.sound']),line
  for dep,pin in r['direct_imports'].items():assert sha(pin['object_path'])==pin['sha256'],dep
  assert r['swaps']==0
  assert r['peak_rss_bytes']<5*2**30
  accepted[r['module']]=r
expected=['S8OwnedP6.Types','S8OwnedP6.Funs','S8OwnedP6LoopContracts','S8OwnedP6ValueModel','S8OwnedP6Finish','S8OwnedP6FieldParserTransport','S8OwnedP6QMParserTransport','S8OwnedP6StrictParser','S8OwnedP6Scan','S8OwnedP6StrictScanModel','S8OwnedP6Residue','S8OwnedP6R14Backend','S8OwnedP6Certificate','S8OwnedP6EndpointAudit']
assert set(accepted)==set(expected),(set(expected)-set(accepted))
for mod,r in accepted.items():
 s=(B/'lean'/(mod.replace('.','/')+'.lean')).read_text()
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',re.sub(r'/\-.*?\-/|--[^\n]*','',s,flags=re.S)),mod
 for thm in re.findall(r'^(?:private )?theorem (\w+)',s,re.M):
  assert '#print axioms '+thm in s,(mod,thm)
for r in host:
 assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 assert r['cgroup_swap_peak_bytes']==0
required=['target','exit_status','wall_seconds','source_revision','source_sha256','deps_fingerprint','print_axioms']
for r in host+proofs:
 for key in required:
  if key=='target' and 'module' in r:continue
  assert key in r,(r['receipt_path'],key)
assert not subprocess.check_output(['git','diff','--name-only','75c037e96','--','crates','programs'],cwd=R,text=True).strip()
assert not subprocess.check_output(['git','diff','--name-only','--diff-filter=MDR','75c037e96','--',str(B/'lean')],cwd=R,text=True).strip(), 'Existing Lean modules edited (new untracked additions are checked separately)'
reused=json.loads((E/'s7-reuse-pins.json').read_text())
for p,h in reused['sources'].items():assert sha(R/p)==h,p
# Explicit successful roots retained even in a timed-out multi-root batch.
roots={
 'kani-02':['proofs::compact_one_chunk','proofs::compact_remainder'],
 'kani-03':['proofs::value_all_u64','proofs::finish_one_row','proofs::finish_step_frame'],
 'kani-05':['proofs::value_contract','proofs::finish_step_verified_value','proofs::compact_step_at_ordinal'],
 'kani-06':['proofs::compact_fixed_y1_29'],
 'kani-08':['proofs::reducer_contract']}
byhost={r['attempt']:r for r in host}
for name,names in roots.items():
 assert name in byhost,name
 log=(E/'receipts'/name/'stdout.log').read_text()
 for h in names:assert 'Checking harness '+h+'...' in log,(name,h)
 assert log.count('VERIFICATION:- SUCCESSFUL')==len(names),(name,'Unexpected successful-root count')
if 'kani-09' in byhost and byhost['kani-09']['exit_status']==0:
 roots['kani-09']=['proofs::finish64_with_verified_reducer']
summary={'schema':'s8-owned-p6-partial-certificate-v1','status':'Complete checked reference/model and frozen production compact scan; S8 headline OPEN pending source finish traversal/caller interpretation','source_revision':accepted['S8OwnedP6Certificate']['source_revision'],'premises_removed':[],'named_reference_certificate':'S8OwnedP6Certificate.reference_model','accepted_lean_modules':sorted(accepted),'accepted_proof_receipts':{m:r['receipt_path'] for m,r in accepted.items()},'axiom_audits':[a for r in accepted.values() for a in r['print_axioms']],'accepted_peak_rss_bytes':max(r['peak_rss_bytes'] for r in accepted.values()),'accepted_swaps':0,'accepted_kani_roots':roots,'new_kani_roots_passed':sum(map(len,roots.values())),'native_comparison_tests':3,'source_finish_loop_contract_obstruction':'kani-10: IterMut lacks KaniIntoIter and Clone in Kani 0.67.0','endpoint_status':'Existing R19 statement byte-identical; generic arbitrary S8 restoration refuted in checked new module','release_replay':False,'all_host_attempts_capped':True,'remaining_file':'remaining.tsv'}
(E/'manifest.json').write_text(json.dumps({'schema':'focused-extractor-proof-packet-v1','proof_attempts':proofs,'host_attempts':host},indent=2)+'\n')
(E/'accepted-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:summary[k] for k in ['status','accepted_peak_rss_bytes','accepted_swaps','new_kani_roots_passed']}))
print('Accepted theorem audits:',len(summary['axiom_audits']))
