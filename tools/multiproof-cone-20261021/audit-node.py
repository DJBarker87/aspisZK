#!/usr/bin/env python3
"""Focused continuation-3 audit, including explicit non-closure boundaries."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent
E=R/'docs/research/100bit-spend-path-20261013/evidence/multiproof-cone-20261021';L=E.parent.parent/'lean'
BASE='feeb8584a'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
git=lambda *a:subprocess.check_output(['git',*a],cwd=R).decode()
subprocess.run(['python3','-B',str(T/'generate.py'),'--check'],check=True)
modules={'MultiproofConeRead32','MultiproofConeNodeDomain','MultiproofConeNodeIteration',
 'MultiproofConeNodeAdoption','MultiproofConeNodeWindow','MultiproofConeModelBoundary','MultiproofConeNodeFreeze'}
current=[a for a in json.loads((E/'manifest.json').read_text())['attempts'] if a['module'] in modules and a['final_current']]
assert {a['module'] for a in current}==modules
allowed={'propext','Classical.choice','Quot.sound'}
for a in current:
 assert a['exit']==0 and not a['errors'] and a['swaps']==0
 source=L/(a['module']+'.lean');assert sha(source)==a['source_sha256']
 snapshot=E/(a['module']+'-'+str(a['attempt']))/'source.lean.txt'
 assert sha(snapshot)==a['source_sha256']
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
 reports=re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",log)
 assert reports==a['axioms'] and 'error:' not in log and 'sorryAx' not in log
 timing=(R/a['time']).read_text()
 assert int(re.search(r'(\d+)\s+maximum resident set size',timing)[1])==a['peak_rss_bytes']
 assert int(re.search(r'(\d+)\s+swaps',timing)[1])==a['swaps']
 command=json.loads((E/(a['module']+'-'+str(a['attempt']))/'command.json').read_text())
 for field in ['module','attempt','source_revision','source_sha256','direct_imports','deps_fingerprint','argv','lean_path']:
  assert command[field]==a[field]
# No existing Lean module or owner candidate is modified. The base comparison
# also excludes all shipped crate changes, so no ELF gate is triggered.
assert not git('diff',BASE,'--','crates','docs/research/100bit-spend-path-20261013/lean-candidates').strip()
for row in git('diff','--name-status',BASE,'--',str(L.relative_to(R))).splitlines():
 assert row.startswith('A\t'),row
# Rust roots are checked against successful immutable snapshots. Runner/docs
# edits after the run cannot relabel any changed executable callee as current.
checks=[]
for name,count in [('cone3-hash-1',1),('cone3-nodes-1',5)]:
 d=E/'host/receipts'/name;r=json.loads((d/'receipt.json').read_text())
 assert r['exit_status']==0 and r['swaps']==0 and r['cgroup_swap_peak_bytes']==0
 assert r['kani_verifier_validation']==dict(expected_harnesses=count,successful_verifier_results=count,failed_verifier_results=0,complete=True)
 assert (d/'stdout.log').read_text().count('VERIFICATION SUCCESSFUL')==count
 assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 for path,pin in r['source_sha256'].items():
  if Path(path).suffix in {'.rs','.toml','.lock'}:
   assert sha(R/path)==pin,path
 for p in (d/'inputs').glob('*.txt'):
  rel=p.name[:-4].replace('--','/')
  if Path(rel).suffix in {'.rs','.toml','.lock'}:
   assert sha(p)==sha(T/rel),rel
 reservation=json.loads((E/'host'/('reservation-'+name+'.json')).read_text())
 assert reservation['allowed'] and reservation['all_populated_scopes_bounded']
 assert reservation['bounded_reserved_bytes']+reservation['requested_bytes']<=reservation['safe_limit_bytes']
 checks.append({k:r[k] for k in ['attempt','source_revision','target','exit_status','wall_seconds','peak_rss_kib','swaps','limits']})
# Unchanged reference/extraction inputs are reused. No fresh source adoption is
# inferred from a compatible cached-object import.
raw='\n'.join(s for s in (T/'src/reference.rs').read_text().splitlines() if not s.startswith('#[cfg_attr(kani,'))+'\n'
ex=json.loads((E/'host/extraction/charon-5-inputs.json').read_text())
assert hashlib.sha256(raw.encode()).hexdigest()==ex['source_sha256']
anchor=next(a for a in current if a['module']=='MultiproofConeNodeFreeze')
result=dict(schema='multiproof-node-continuation-audit-v1',audited_revision=git('rev-parse','HEAD').strip(),
 status='PASS focused node certificates and kernel composition; whole multiproof cone remains BLOCKED',
 focused_lean_modules=sorted(modules),axiom_reports=sum(len(a['axioms']) for a in current),allowed_axioms=sorted(allowed),
 anchor={k:anchor[k] for k in ['module','attempt','source_revision','source_sha256','exit','wall_seconds','peak_rss_bytes','swaps','axioms']},
 rust_certificates=checks,
 exact_target='OraclePortFrozen2Join.AcceptedRunJoin against OraclePortFrozen2.dV_frozen2',
 replacement_scope='one binary parent, arbitrary 0..32-byte window at relative cursor zero; no row or level stubs',
 kernel_result='actual extracted node progress, finite level identity, derived successful-level preservation and conditional height-18 node adoption',
 assumptions=dict(retained=['one-node source-to-extracted full-Result equation on RowDomain; not instantiated by the window gate alone'],
  added=['HashTotal, needed for actual extracted totality/progress'],
  discharged=['complete-level equality and level-preservation premises for the specific bounded rows source-level constructor'],
  carrier_change='source is now a node Step, level is defined by bounded rows; this is not unqualified premise deletion for arbitrary source-level functions'),
 blocked=['production physical .get/window/cursor frame adoption',
  'sorted live-prefix and scratch-suffix/safe-overwrite simulation to runLevel, including ordered logs',
  'initial-key/opening, leaf/count/padding/root adapters and both three-slot batch stages'],
 diagnostic='descending_source hashes (1,0), descending_model rejects it; paired_iff needs ascending order; no reached-source counterexample claimed',
 coherent_frozen_manifest_replayed=False,shipped_sources_unchanged=True,sibling_candidates_unchanged=True,
 frozen_elf_rebuild_required=False,frozen_elf_identity_measured=False,
 complete_multiproof_source_cone=False,accepted_run_join_constructed=False,caller_lowering_attempted=False)
(E/'audit-node-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','focused_lean_modules','axiom_reports','complete_multiproof_source_cone','accepted_run_join_constructed']},indent=2))
