#!/usr/bin/env python3
"""Audit only this continuation. Historical packet audits remain historical."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent
E=R/'docs/research/100bit-spend-path-20261013/evidence/multiproof-cone-20261021';L=E.parent.parent/'lean'
BASE='5b24889edc8e9951466a71931d1c5c8f0899896c'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
git=lambda *a:subprocess.check_output(['git',*a],cwd=R)
subprocess.run(['python3','-B',str(T/'generate.py'),'--check'],check=True)
modules={'MultiproofConeSortInsertion','MultiproofConeSortTotal','MultiproofConeSortOrder',
         'MultiproofConeSortPermutation','MultiproofConeLevelIteration','MultiproofConeContinuationFreeze'}
current=[a for a in json.loads((E/'manifest.json').read_text())['attempts'] if a['module'] in modules and a['final_current']]
assert {a['module'] for a in current}==modules
allowed={'propext','Classical.choice','Quot.sound'}
for a in current:
 assert a['exit']==0 and not a['errors'] and a['swaps']==0
 assert sha(L/(a['module']+'.lean'))==a['source_sha256']
 assert all(sha(Path(p['path']))==p['sha256'] for p in a['direct_imports'])
 assert sha(Path(a['argv'][a['argv'].index('-o')+1]))==a['object_sha256']
 source=(L/(a['module']+'.lean')).read_text()
 assert not re.search(r'\b(?:sorry|axiom|admit|native_decide)\b|set_option\s+(?:maxRecDepth|maxHeartbeats)',source)
 for name in re.findall(r'^(?:private )?theorem\s+(\w+)',source,re.M):assert '#print axioms '+name in source
 assert a['axioms']
 for report in a['axioms']:
  if 'does not depend on any axioms' in report:continue
  assert {s.strip() for s in re.search(r'\[([^]]*)\]',report)[1].split(',')}<=allowed
# Source ownership: no shipped crates or Session A/sibling candidates changed.
assert not git('diff',BASE,'--','crates','docs/research/100bit-spend-path-20261013/lean-candidates').strip()
for row in git('diff','--name-status',BASE,'--',str(L.relative_to(R))).decode().splitlines():
 assert row.startswith('A\t'),row
# The references remain exactly the retained extracted Rust inputs. Kani-only
# attributes do not enter Charon/Aeneas extraction.
raw='\n'.join(s for s in (T/'src/reference.rs').read_text().splitlines() if not s.startswith('#[cfg_attr(kani,'))+'\n'
ex=json.loads((E/'host/extraction/charon-5-inputs.json').read_text())
assert hashlib.sha256(raw.encode()).hexdigest()==ex['source_sha256']
sortrec=json.loads((E/'host/receipts/sort-charon-2/receipt.json').read_text())
assert sha(T/'src/sort_reference.rs')==sortrec['source_sha256']['tools/multiproof-cone-20261021/src/sort_reference.rs']
# The final leaf certificate is reused across an unrelated binary-row harness
# attribute change. Check its exact root blocks and every executable callee file.
leafdir=E/'host/receipts/cone2-leaf-2'
leaf=json.loads((leafdir/'receipt.json').read_text())
assert leaf['exit_status']==0 and leaf['swaps']==0 and leaf['kani_verifier_validation']['complete']
assert leaf['kani_verifier_validation']['successful_verifier_results']==2
assert (leafdir/'stdout.log').read_text().count('VERIFICATION SUCCESSFUL')==2
assert leaf['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
for path,pin in leaf['source_sha256'].items():
 if path.startswith('crates/aspis-core/src/') or path in [
     'tools/multiproof-cone-20261021/src/adoption.rs',
     'tools/multiproof-cone-20261021/src/frozen.rs','tools/multiproof-cone-20261021/src/reference.rs',
     'tools/multiproof-cone-20261021/Cargo.toml','tools/multiproof-cone-20261021/Cargo.lock']:
  assert sha(R/path)==pin,path
proofpath='tools/multiproof-cone-20261021/src/proofs.rs'
old=git('show',leaf['source_revision']+':'+proofpath).decode();now=(R/proofpath).read_text()
def block(s,name):
 pos=s.index('fn '+name+'(');start=s.rfind('\n\n',0,pos);b=s.index('{',pos);depth=1;e=b+1
 while depth:depth+=(s[e]=='{')-(s[e]=='}');e+=1
 return s[start:e]
for name in ['adoption_leaf_hash_contract','adoption_leaf_batch_step']:assert block(old,name)==block(now,name)
# A nonzero/empty result is retained as failed evidence, never as a verified
# prerequisite of the composed level harness.
failed=[]
for name in ['cone2-level-step-1','cone2-row-contract-1','cone2-row-contract-inline-1']:
 p=E/'host/receipts'/name
 rec=json.loads((p/'receipt.json').read_text())
 assert rec['exit_status']!=0 and not rec['kani_verifier_validation']['complete']
 assert rec['kani_verifier_validation']['successful_verifier_results']==0
 assert rec['swaps']==0
 assert rec['limits']==leaf['limits']
 failed.append({k:rec[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','cgroup_memory_peak_bytes']})
anchor=next(a for a in current if a['module']=='MultiproofConeContinuationFreeze')
result=dict(schema='multiproof-cone-continuation-audit-v1',
 status='PASS: sort closure, leaf step certificate and focused standard-axiom audit; binary adoption BLOCKED',
 audited_revision=git('rev-parse','HEAD').decode().strip(),
 sort_reference_and_frozen_order='proved',leaf_batch_step='P6 verified with verified leaf-hash callee',
 binary_row_contract='not verified; both bounded attempts timed out',
 binary_level_composed='not run: verified-callee prerequisite missing',
 height_iteration='kernel full-Result identity to extracted levels; source adoption remains conditional on local certificate and preservation',
 focused_lean_modules=sorted(modules),axiom_reports=sum(len(a['axioms']) for a in current),
 axioms=sorted(allowed),anchor={k:anchor[k] for k in ['module','attempt','source_revision','source_sha256','exit','wall_seconds','peak_rss_bytes','swaps','axioms']},
 leaf_receipt={k:leaf[k] for k in ['source_revision','target','exit_status','wall_seconds','peak_rss_kib','swaps','limits']},
 failed_binary_gates=failed,
 reference_source_sha256=sha(T/'src/reference.rs'),reference_extraction_source_sha256=ex['source_sha256'],
 extracted_reference_Funs_sha256=sha(L/'MultiproofConeRef/Funs.lean'),
 sort_reference_source_sha256=sha(T/'src/sort_reference.rs'),extracted_sort_Funs_sha256=sha(L/'MultiproofSortRef/Funs.lean'),
 shipped_sources_unchanged=True,sibling_candidates_unchanged=True,
 complete_parser_source_cone=False,complete_multiproof_source_cone=False,accepted_run_join_constructed=False,
 caller_lowering_attempted=False,coherent_frozen_manifest_replayed=False,
 frozen_elf_rebuild_required=False,frozen_elf_identity_measured=False)
(E/'audit-continuation-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
