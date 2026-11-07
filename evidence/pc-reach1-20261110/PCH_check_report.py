"""Consistency check of blocked reporting only; NOT the graph mutation validator."""
import pathlib,json,hashlib,subprocess
E=pathlib.Path(__file__).resolve().parent;R=E.parents[1];load=lambda n:json.loads((E/n).read_text())
a=load('PCH_AUTHORITY.json');assert not a['admitted'] and a['retained_elf_hash_comparison']['matches']
for name,p in a['input_pins'].items():assert hashlib.sha256((R/name).read_bytes()).hexdigest()==p['sha256'],name
for p in a['artifacts']:assert hashlib.sha256((R/p['path']).read_bytes()).hexdigest()==p['sha256']
v=load('PCH_VERDICTS.json')['rows'];assert len(v)==len({r['row'] for r in v})==278
assert all(r['verdict'] is None and r['assessment_status']=='NOT_ASSESSED_AUTHORITY_BLOCKED' for r in v)
assert sum(r['inherited_status']=='CLOSED' for r in v)==39
assert load('PCH_LEDGER_DELTA.json')['rows']==[]
assert all(x=='NOT_RUN' for x in load('PCH_VALIDATION.json')['mutation_tests'].values())
assert load('PCH_VALIDATION.json')['validator_exit_status'] is None
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20_000_000,p
assert not list(E.rglob('__pycache__'))
tracked=subprocess.check_output(['git','diff','--name-only','HEAD'],cwd=R,text=True).splitlines()
assert all(p.startswith(str(E.relative_to(R))+'/') for p in tracked)
print('PCH blocked-report consistency PASS; graph mutation tests NOT RUN')
