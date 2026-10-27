"""Validate the recount packet and its source/receipt boundaries."""
from pathlib import Path
import hashlib, json, subprocess
E=Path(__file__).resolve().parent
R=E.parents[1]
def get(p): return json.loads((E/p).read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
x=get('Rc12_LEDGER_DELTA.json')
for pin in get('Rc12_INPUT_PINS.json'):
    assert sha(R/pin['path'])==pin['sha256'],pin['path']
    assert (R/pin['path']).stat().st_size==pin['bytes']
assert len(x['new_deployment_rows'])==15
assert len({r['id'] for r in x['new_deployment_rows']})==15
assert sum(c['delta_P'] for c in x['changes'])==14
assert all(r['classification']=='P' and r['owner']=='lead' for r in x['new_deployment_rows'])
for root,d in x['roots'].items():
    assert (E/f'Rc12_{root}.BEFORE.lean.txt').read_bytes()==(E/f'Rc12_{root}.AFTER.lean.txt').read_bytes()
    for scope in ['actual antecedent','deployment only','deployment alias','deployment-inclusive non-alias','raw including alias']:
        rows=[r for r in d['rows'] if scope=='raw including alias' or (scope=='deployment-inclusive non-alias' and r['scope']!='deployment alias') or r['scope']==scope]
        assert d['after'][scope]=={c:sum(r['classification']==c for r in rows) for c in 'TPGC'}
    assert d['before']['actual antecedent']==d['after']['actual antecedent']
    assert not any(r['id']=='L187' for r in d['rows'])
    assert d['after']['deployment-inclusive non-alias']['P'] in [30,28]
r=get('Rc12_001/receipt.json')
assert r['exit_status']==0
assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
assert '-M7000' in r['command']
assert r['source_hashes']['Rc12_Audit.lean']==sha(R/'lean/Rc12_Audit.lean')
assert sha(E/'Rc12_001/sources/Rc12_Audit.lean')==sha(R/'lean/Rc12_Audit.lean')
for line in r['print_axioms']:
    assert line.endswith('[propext, Classical.choice, Quot.sound]'),line
assert len(list(E.glob('Rc12_*/receipt.json')))==1
assert get('Rc12_001-retries.json')==[]
assert get('Rc12_statement-check.json')['complete_retained_root_types_in_fresh_output']
paths=subprocess.check_output(['git','diff','--name-only','780f798237'],cwd=R,text=True).splitlines()
untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines()
assert all(p.startswith('evidence/recount12-20261027/Rc12_') or p=='lean/Rc12_Audit.lean' for p in paths+untracked),(paths,untracked)
assert not any(p.suffix in ['.olean','.elf','.so','.tar','.gz'] for p in E.rglob('*') if p.is_file())
result=dict(status='pass',checked_input_pins=len(get('Rc12_INPUT_PINS.json')),new_deployment_rows=15,net_deployment_P_delta=14,actual_delta=0,Lean_attempts=1,Kani_runs=0,all_printed_axioms_standard=True,no_shipped_or_authoritative_edits=True,source_revision=r['source_revision'],target='Rc12_Audit',exit_status=0,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'])
(E/'Rc12_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
