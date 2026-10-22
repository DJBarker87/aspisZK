#!/usr/bin/env python3
"""Focused continuation-4 audit. No relabelling of whole-cone closure."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent
E=R/'docs/research/100bit-spend-path-20261013/evidence/multiproof-cone-20261021';L=E.parent.parent/'lean'
BASE='01b350ddf'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
git=lambda *args:subprocess.check_output(['git',*args],cwd=R,text=True)
subprocess.run(['python3','-B',str(T/'generate.py'),'--check'],check=True)
modules={'MultiproofConeLiveOrder','MultiproofConeLiveLeaves','MultiproofConeLiveReference',
 'MultiproofConeLivePreservation','MultiproofConeLiveBatch','MultiproofConeLiveFold','MultiproofConeOrderedLevel','MultiproofConeLiveFreeze'}
current=[a for a in json.loads((E/'manifest.json').read_text())['attempts'] if a['module'] in modules and a['final_current']]
assert {a['module'] for a in current}==modules
allowed={'propext','Classical.choice','Quot.sound'}
for a in current:
 assert a['exit']==0 and not a['errors'] and a['swaps']==0
 source=L/(a['module']+'.lean');assert sha(source)==a['source_sha256']
 folder=E/(a['module']+'-'+str(a['attempt']))
 assert sha(folder/'source.lean.txt')==a['source_sha256']
 assert all(sha(p['path'])==p['sha256'] for p in a['direct_imports'])
 assert sha(a['argv'][a['argv'].index('-o')+1])==a['object_sha256']
 text=source.read_text()
 assert not re.search(r'\b(?:sorry|axiom|admit|native_decide)\b|set_option\s+(?:maxRecDepth|maxHeartbeats)',text)
 for theorem in re.findall(r'^(?:private )?(?:@\[[^\n]+\] )?theorem\s+(\w+)',text,re.M):
  assert '#print axioms '+theorem in text,(a['module'],theorem)
 assert a['axioms']
 for report in a['axioms']:
  if 'does not depend on any axioms' not in report:
   assert {s.strip() for s in re.search(r'\[([^]]*)\]',report)[1].split(',')}<=allowed
 log=(R/a['log']).read_text()
 assert re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",log)==a['axioms']
 assert 'error:' not in log and 'sorryAx' not in log
 timing=(R/a['time']).read_text()
 assert int(re.search(r'(\d+)\s+maximum resident set size',timing)[1])==a['peak_rss_bytes']
 assert int(re.search(r'(\d+)\s+swaps',timing)[1])==a['swaps']
 command=json.loads((folder/'command.json').read_text())
 for field in ['module','attempt','source_revision','source_sha256','direct_imports','deps_fingerprint','argv','lean_path']:
  assert command[field]==a[field]
assert not git('diff',BASE,'--','crates','docs/research/100bit-spend-path-20261013/lean-candidates').strip()
for row in git('diff','--name-status',BASE,'--',str(L.relative_to(R))).splitlines():
 assert row.startswith('A\t'),row
checks=[]
for name,count in [('cone4-order-1',2),('cone4-physical-1',3),('cone4-keys-1',1),('cone3-hash-1',1),('cone3-nodes-1',5)]:
 d=E/'host/receipts'/name;r=json.loads((d/'receipt.json').read_text())
 assert r['exit_status']==0 and r['swaps']==0 and r['cgroup_swap_peak_bytes']==0
 assert r['kani_verifier_validation']==dict(expected_harnesses=count,successful_verifier_results=count,failed_verifier_results=0,complete=True)
 assert (d/'stdout.log').read_text().count('VERIFICATION SUCCESSFUL')==count
 assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 for path,pin in r['source_sha256'].items():
  if Path(path).suffix in {'.rs','.toml','.lock'}:
   if path in {'tools/multiproof-cone-20261021/src/lib.rs','tools/multiproof-cone-20261021/src/proofs.rs'}:
    # Later stages append declarations/harnesses, preserving each tested prefix.
    snap=d/'inputs'/('src--'+Path(path).name+'.txt')
    assert sha(snap)==pin
    assert (R/path).read_bytes().startswith(snap.read_bytes()),path
   else: assert sha(R/path)==pin,path
 for p in (d/'inputs').glob('*.txt'):
  rel=p.name[:-4].replace('--','/')
  if Path(rel).suffix in {'.rs','.toml','.lock'}:
   if rel in {'src/lib.rs','src/proofs.rs'}:assert (T/rel).read_bytes().startswith(p.read_bytes())
   else:assert sha(p)==sha(T/rel),rel
 reservation=json.loads((E/'host'/('reservation-'+name+'.json')).read_text())
 assert reservation['allowed'] and reservation['all_populated_scopes_bounded']
 assert reservation['bounded_reserved_bytes']+reservation['requested_bytes']<=reservation['safe_limit_bytes']
 checks.append({k:r[k] for k in ['attempt','source_revision','target','exit_status','wall_seconds','peak_rss_kib','swaps','limits']})
anchor=next(a for a in current if a['module']=='MultiproofConeLiveFreeze')
result=dict(schema='multiproof-live-continuation-audit-v1',audited_revision=git('rev-parse','HEAD').strip(),
 status='PASS focused live-order and physical-window gates; whole cone remains open',
 focused_lean_modules=sorted(modules),axiom_reports=sum(len(a['axioms']) for a in current),allowed_axioms=sorted(allowed),
 anchor={k:anchor[k] for k in ['module','attempt','source_revision','source_sha256','exit','wall_seconds','peak_rss_bytes','swaps','axioms']},
 rust_certificates=[c for c in checks if c['attempt'].startswith('cone4-')],
 reused_rust_certificates=[c for c in checks if c['attempt'].startswith('cone3-')],exact_target='OraclePortFrozen2Join.AcceptedRunJoin against OraclePortFrozen2.dV_frozen2',
 physical_scope='arbitrary 5504-byte storage, arbitrary bounded length and cursor; occupied/sibling/short; exact scratch and hash observations; no reader/row/level stubs',
 discharged=['mathematical mixed-prefix order preservation','actual extracted successful-node and level order preservation','bounded physical-to-window P6 cursor/frame gate'],
 retained=['P6 operational/source translation and loop factoring','HashTotal for extracted node progress/order induction'],
 remaining=['reached batch source-loop/key/opening carrier instantiation','ordered source log to frozen runLevel simulation','count/padding/root and both three-slot batch adapters'],
 coherent_frozen_manifest_replayed=False,shipped_sources_unchanged=True,sibling_candidates_unchanged=True,
 frozen_elf_rebuild_required=False,frozen_elf_identity_measured=False,
 complete_multiproof_source_cone=False,accepted_run_join_constructed=False,caller_lowering_attempted=False)
(E/'audit-live-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','focused_lean_modules','axiom_reports','complete_multiproof_source_cone','accepted_run_join_constructed']},indent=2))
