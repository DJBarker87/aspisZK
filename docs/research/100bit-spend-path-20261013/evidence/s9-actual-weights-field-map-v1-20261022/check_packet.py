from pathlib import Path
import hashlib,json,re
p=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
m=json.loads((p/'manifest.json').read_text()); ident=json.loads((p/m['source_identity']).read_text()); e=m['entries'][0]
r=json.loads((p/e['receipt']).read_text()); pre=json.loads((p/e['preflight']).read_text()); log=(p/e['log']).read_text()
assert m['schema']=='focused-extractor-proof-packet-v1' and m['compiled_objects_included'] is False
assert r==e['launch_metrics'] and r['exit_status']==0 and r['process_swaps']==0 and r['watchdog_abort'] is None and r['foreign_lean_samples']==[]
assert sha(p/e['source'])==e['source_sha256']==r['source_sha256']==pre['source_sha256'] and r['object_sha256']==e['object_sha256']
assert pre['direct_imports']==e['direct_imports']
for x in e['direct_imports'].values(): assert Path(x['path']).is_file() and sha(Path(x['path']))==x['sha256']
reports=re.findall(r"'AspisR1S9ActualWeightsFieldOwnedMapV1.actual_weights_field_maps_to_owned' depends on axioms:\s*\[(.*?)\]",log,re.S); assert len(reports)==1 and set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*',reports[0]))=={'propext','Classical.choice','Quot.sound'}
base=Path('/Users/dominic/ZK/docs/research/100bit-spend-path-20261013')
for key in ('raw_generated_funs','rust_source'):
 q=base/ident[key]['path']; assert q.is_file() and sha(q)==ident[key]['sha256']
raw=(base/ident['raw_generated_funs']['path']).read_text(); copied=(p/e['source']).read_text()
def norm(t,a,b):
 i=t.index(a);j=t.index(b,i);return re.sub(r'\s+',' ',t[i:j]).strip()
assert norm(raw,'def weights.field','\nend AspisR1S9ActualFieldTypesCutV1')==norm(copied,'def weights.field','\nend AspisR1S9ActualFieldTypesCutV1')
assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',re.sub(r'/\-.*?\-/','',copied,flags=re.S))
for ext in ('*.olean','*.elf','*.so','*.pyc'): assert not list(p.rglob(ext))
for line in (p/'SHA256SUMS').read_text().splitlines(): d,rel=line.split('  ',1);assert sha(p/rel)==d
print('PASS: source/import pins, exact extracted declaration, successful receipt, standard axiom report; no binaries')
