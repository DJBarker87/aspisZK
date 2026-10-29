from pathlib import Path
import ast,json,hashlib,subprocess
E=Path('evidence/pv-cx2-20261029')
x=json.loads((E/'translator-identity.json').read_text());assert x['status']=='functionally identical rebuild (ae1-2)'
assert all(r['passed'] for r in x['raw_comparisons']);assert all(r['equal'] for r in x['ProverRwFull_comparisons'])
a=json.loads((E/'historical-caller-dictionary-adapter.json').read_text());b=json.loads((E/'rebuilt-caller-dictionary-adapter.json').read_text());assert a['outputs']==b['outputs']
for p in Path('tools/pv-cx2-20261029').glob('*.py'):ast.parse(p.read_text())
old=json.loads(Path('evidence/pv-cx-20261029/effect-interface.json').read_text());new=json.loads((E/'effect-interface.json').read_text());ids=[]
for a,b in zip(old['opaque_functions'],new['opaque_functions'],strict=True):
 for k in ['llbc_fun_id','rust_path','signature_llbc','source_call_sites','generics_llbc']:assert a[k]==b[k]
 if not a['effect_class']:
  ids.append(a['llbc_fun_id']);assert b['effect_class'] and b['classification_evidence']
assert len(ids)==62 and all(r['effect_class'] for r in new['opaque_functions'])
assert subprocess.check_output(['git','diff','570c000809','--','crates/','programs/','tools/r1-cost-probe/'])==b''
receipts=[]
for p in sorted(E.glob('N*/receipt.json')):
 r=json.loads(p.read_text());assert r['limits']==dict(zip(['memory.high','memory.max','memory.swap.max','pids.max'],[str(6*2**30),str(8*2**30),'0','64']))
 assert r['swaps']==0
 q=json.loads((p.parent/'reservation-before.json').read_text());assert q['allowed'] is True
 q=json.loads((p.parent/'reservation-at-barrier.json').read_text());assert q['allowed'] is True
 receipts.append(dict(attempt=p.parent.name,exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps']))
assert len(receipts)<=20
assert not [str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*2**20]
result=dict(identity_pass=True,adapter_outputs_equal=True,resolved_empty_classifications=ids,source_and_call_sites_preserved=True,frozen_source_unchanged=True,native_runs=receipts,lean_attempts=0,kani_attempts=0,rows_removed=[],note='No Lean elaboration or axioms audit claimed until there are explicit Lean receipts.')
(E/'validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(native_runs=len(receipts),classifications=len(ids),frozen_source_unchanged=True)))
