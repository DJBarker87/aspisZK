"""Check this task's evidence and accepted source tree without compiling again."""
from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent.parent
L=Path('docs/research/v8-r0-zk-20261009/lean')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
records=json.loads((E/'lean/attempts.json').read_text())
retired=[json.loads(p.read_text()) for p in (E/'pins').glob('retired-*.json')]
used={r['attempt'] for r in records};ret={r['attempt'] for r in retired}
assert used.isdisjoint(ret)
assert used|ret==set(range(10300,10369))
assert all(10300<=r['attempt']<=10399 for r in records)
for r in records:
 assert sha(E/r['source_snapshot'])==r['source_sha256']
 assert r['wall'] and r['peak_rss_kib'] and r['swaps'] is not None
 assert len(r['deps_fingerprint'])==64 and r['source_revision']
accepted={}
for r in records:
 if r['exit_status']==['0']:accepted[r['module']]=r
freeze=[]
for module,r in sorted(accepted.items()):
 p=L/module
 if not p.exists():continue # Retained throwaway diagnostic snapshot only.
 assert sha(p)==r['source_sha256'],p
 assert not re.search(r'\b(sorry|admit|native_decide|sorryAx)\b|set_option\s+(maxRecDepth|maxHeartbeats)',p.read_text()),p
 for line in r['print_axioms']:
  if 'depends on axioms:' in line:
   assert set(re.findall(r'[A-Za-z][A-Za-z.]*',line.split('depends on axioms:')[1]))<={'propext','Classical.choice','Quot.sound'},line
 freeze.append(dict(source=str(p),sha256=sha(p),accepted_attempt=r['attempt']))
audit=next(r for r in records if r['attempt']==10368)
assert audit['exit_status']==['0'] and not audit['errors']
plan=json.loads((E/'pins/final-audit-plan.json').read_text())
for theorem in plan['new_audits']:
 assert any(line.startswith("'"+theorem+"'") for line in audit['print_axioms']),theorem
assert (E/'endpoint/before.lean.txt').read_bytes()==(E/'endpoint/after.lean.txt').read_bytes()==(L/'R1Z/ProverCommitDeployedFuel22.lean').read_bytes()
base=(E/'pins/revision.txt').read_text().strip()
subprocess.run(['git','diff','--exit-code',base,'--','crates','programs'],check=True)
assert not subprocess.check_output(['git','ls-files','--others','--exclude-standard','--','crates','programs'],text=True).strip()
files=subprocess.check_output(['git','ls-files','--','crates','programs'],text=True).splitlines()
ship=dict(base_revision=base,file_count=len(files),files=[dict(path=p,sha256=sha(Path(p)),size=Path(p).stat().st_size) for p in files],unchanged_by_git_diff=True,elf_rebuild_triggered=False,qualification='No shipped source changed. Prior frozen ELF pins retained; no fresh ELF identity claim.')
(E/'pins/final-shipped-inventory.json').write_text(json.dumps(ship,indent=2)+'\n')
for p in E.rglob('*'):
 assert p.name!='target',p
 assert not p.is_file() or p.suffix not in {'.olean','.llbc','.elf','.tar','.gz'},p
(E/'pins/final-lean-freeze.json').write_text(json.dumps(dict(modules=freeze,public_audits=plan['new_audits']),indent=2)+'\n')
result=dict(source_revision=base,accepted_cone_source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),allocated_attempts_used=[10300,10368],compiler_attempts=len(records),retired_preflights=len(retired),successful_compiler_attempts=sum(r['exit_status']==['0'] for r in records),remaining_range=[10369,10399],frozen_current_modules=len(freeze),final_audit_attempt=10368,final_audit_exit=0,final_audit_wall=audit['wall'],final_audit_peak_rss_kib=audit['peak_rss_kib'],final_audit_swaps=audit['swaps'],new_axiom_audits=len(plan['new_audits']),total_final_axiom_prints=len(audit['print_axioms']),accepted_axioms_standard=True,endpoint_unchanged=True,shipped_files_unchanged=True,elf_rebuild_triggered=False,full_terminal_oracle_proved=False,full_simulator_payload_equality_proved=False,final_release_claim=False)
(E/'pins/final-integrity-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
