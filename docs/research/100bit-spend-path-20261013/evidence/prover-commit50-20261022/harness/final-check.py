from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent.parent;L=Path('docs/research/v8-r0-zk-20261009/lean')
records=json.loads((E/'lean/attempts.json').read_text());retired=json.loads((E/'pins/retired-attempts.json').read_text())
assert {r['attempt'] for r in records}|{r['attempt'] for r in retired}==set(range(10200,10300))
assert not ({r['attempt'] for r in records}&{r['attempt'] for r in retired})
freeze=json.loads((E/'pins/final-lean-freeze.json').read_text())
for r in freeze['modules']:
 p=Path(r['source']);assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256']
 accepted=[a for a in records if a['attempt']==r['accepted_attempt']]
 assert len(accepted)==1 and accepted[0]['exit_status']==['0']
 assert not re.search(r'\b(sorry|admit|native_decide|sorryAx)\b|set_option\s+(maxRecDepth|maxHeartbeats)',p.read_text())
 for ax in accepted[0]['print_axioms']:
  tail=ax.split('depends on axioms:')[-1]
  if '[' in tail:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',tail))<={'propext','Classical.choice','Quot.sound'}
endpoint=L/'R1Z/ProverCommitDeployedFuel22.lean'
assert endpoint.read_bytes()==(E/'endpoint/before.lean.txt').read_bytes()==(E/'endpoint/after.lean.txt').read_bytes()
base=(E/'pins/revision.txt').read_text().strip()
subprocess.run(['git','diff','--exit-code',base,'--','crates','programs'],check=True)
assert not subprocess.check_output(['git','ls-files','--others','--exclude-standard','--','crates','programs'],text=True).strip()
for p in E.rglob('*'):
 assert not p.is_file() or p.suffix not in ['.olean','.llbc','.elf','.tar','.gz'],p
 assert p.name!='target',p
# Inspect the actual integration collision without changing accepted sources.
def decl(p,name):
 s=p.read_text();a=s.index('def '+name+'\n');ends=[x for x in [s.find('\ndef ',a+1),s.find('\nend ',a+1)] if x>=0];return s[a:min(ends)].strip()
a=L/'AspisR1ProducerRelease47/Linear50.lean';b=L/'AspisR1ProducerRelease47/Batched48.lean'
collision=[]
for name in ['field.CM31.mul_m31','field.QM31.mul_m31']:
 x,y=decl(a,name),decl(b,name);assert x==y
 collision.append(dict(declaration=name,identical_body_sha256=hashlib.sha256(x.encode()).hexdigest()))
(E/'pins/integration-collision.json').write_text(json.dumps(dict(attempt=10299,exit_status=1,modules=[str(a),str(b)],identical_declarations=collision,remedy='Reuse the two byte-identical declarations by importing Batched48 in Linear50 and removing the local duplicates, then rebuild all affected dependents with new attempts before auditing again. No source repair is made after the assigned budget is exhausted.',rebuild_order=['AspisR1ProducerRelease47.Linear50','R1Z.ProverCommitScale50','R1Z.ProverCommitLinearLoop50','R1Z.ProverCommitLinear50','AspisR1ProducerRelease47.MaskFinish50','R1Z.ProverCommitMaskFinish50']),indent=2)+'\n')
result=dict(attempt_range=[10200,10299],compiler_attempts=len(records),retired_preflights=len(retired),successful_compiler_attempts=sum(r['exit_status']==['0'] for r in records),frozen_focused_modules=len(freeze['modules']),public_theorems=len(freeze['public_theorems']),all_current_focused_source_hashes_match=True,all_accepted_printed_axioms_standard=True,endpoint_snapshots_unchanged=True,shipped_files_unchanged=True,shipped_inventory_count=491,elf_rebuild_triggered=False,integrated_audit_passed=False,integrated_audit_attempt=10299,integrated_audit_failure='duplicate mul_m31 declaration imported from Batched48 and Linear50',rejected_kernel_attempt=10298,source_revision=base,audit_source_revision=(E/'pins/audit-source-revision.txt').read_text().strip(),final_release_claim=False)
(E/'pins/final-integrity-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
