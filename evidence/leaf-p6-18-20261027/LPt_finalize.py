"""Read-only terminal evidence audit; never launches a prover or changes caches."""
from pathlib import Path
import json,hashlib,re,subprocess,shlex,time
E=Path(__file__).resolve().parent
# Reuse the own inventory reader, selecting terminal output filenames only.
code=(E/'LPt_inventory.py').read_text().replace('LPt_CACHE_START','LPt_CACHE_END').replace('LPt_LIBRARY_START','LPt_LIBRARY_END')
exec(compile(code,str(E/'LPt_inventory.py'),'exec'))
start=json.loads((E/'LPt_CACHE_START.json').read_text());end=json.loads((E/'LPt_CACHE_END.json').read_text())
assert all(end.get(k)==v for k,v in start.items()),'pre-existing cache changed'
assert json.loads((E/'LPt_LIBRARY_START.json').read_text())==json.loads((E/'LPt_LIBRARY_END.json').read_text()),'resolved Aeneas changed'
assert json.loads((E/'LPt_LIBRARY_PIN.json').read_text())==json.loads((E/'LPt_LIBRARY_END.json').read_text()),'library pin mismatch'
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('LPt_L*/receipt.json'))]
assert len(receipts)<=100
latest={r['module']:r for r in receipts if r['exit_status']==0}
accepted={}
for p in sorted(Path('lean').glob('LPt_*.lean')):
 r=latest[p.stem];sha=hashlib.sha256(p.read_bytes()).hexdigest()
 assert sha in r['source_hashes'].values(),p
 accepted[str(p)]=dict(attempt=r['attempt'],sha256=sha,axioms=r['print_axioms'])
for r in receipts:
 a=r['attempt'];reservation=json.loads((E/(a+'-reservation.json')).read_text())
 assert reservation['allowed'] is True
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert '-M7000' in r['command'] and '-j1' in r['command']
 assert int(r['swaps'])==0
 if r['exit_status']==0:
  for line in r['print_axioms']:
   if 'depends on axioms:' in line:
    axioms=line.split('depends on axioms: ')[1].strip('[]').split(', ')
    assert set(axioms)<=set(['propext','Classical.choice','Quot.sound']),line
# Final imported audit covers every newly declared named theorem, including copies.
audit=latest['LPt_Audit'];names=json.loads((E/'LPt_THEOREMS.json').read_text())
for n in names:assert any(line.startswith("'"+n+"'") for line in audit['print_axioms']),n
scope=subprocess.check_output(['git','diff','--name-only','974db87027','--'],text=True).splitlines()
scope+=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],text=True).splitlines()
scope=sorted(set(scope))
assert all(p.startswith(('lean/LPt_','evidence/leaf-p6-18-20261027/')) for p in scope)
summary=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),lean_attempts=len(receipts),lean_passed=sum(r['exit_status']==0 for r in receipts),kani_runs=0,failures=[dict(attempt=r['attempt'],exit=r['exit_status']) for r in receipts if r['exit_status']],wall_seconds=sum(r['wall_seconds'] for r in receipts),max_peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swaps=0,accepted_sources=accepted,audited_theorems=len(names),cache_start_files=len(start),cache_end_files=len(end),existing_cache_unchanged=True,persistent_cache_retained=True,resolved_aeneas_unchanged=True,full_manifest_replay=False,headline_premises_removed=0,prepared_claim='CLOSED in inherited local native leaf domain',remaining_headline='S2 and deployed100-bit target not established')
(E/'LPt_FINAL_AUDIT.json').write_text(json.dumps(summary,indent=2)+'\n')
(E/'LPt_SCOPE.json').write_text(json.dumps(dict(base='974db87027',source_revision=summary['source_revision'],changed_paths=scope,shipped_changes=False,elf_rebuild_triggered=False),indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ['accepted_sources']}))
