from pathlib import Path
import hashlib,json,re
p=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
m=json.loads((p/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1' and m['compiled_objects_included'] is False
for e in m['entries']:
 r=json.loads((p/e['receipt']).read_text()); pre=json.loads((p/e['preflight']).read_text()); cmd=json.loads((p/e['command']).read_text()); log=(p/e['log']).read_text(); s=p/e['source']
 assert r['exit_status']==0 and r['process_swaps']==0 and r['watchdog_abort'] is None and r['foreign_lean_samples']==[]
 assert sha(s)==e['source_sha256']==r['source_sha256']==pre['source_sha256'] and r['object_sha256']==e['object_sha256']
 assert pre['direct_imports']==e['direct_imports']
 for x in e['direct_imports'].values(): assert Path(x['path']).is_file() and sha(Path(x['path']))==x['sha256']
 for n,ax in e['theorems'].items():
  reports=re.findall("'"+re.escape(n)+r"' depends on axioms:\s*\[(.*?)\]",log,re.S); assert len(reports)==1
  assert set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*',reports[0]))==set(ax) and set(ax)<={'propext','Classical.choice','Quot.sound'}
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',re.sub(r'/\-.*?\-/','',s.read_text(),flags=re.S))
for key in ('actual_attempt7_generated_funs','rust_attempt7_source_span'):
 pin=m['source_pins'][key]; q=Path('/Users/dominic/ZK/docs/research/100bit-spend-path-20261013')/pin['path']; assert q.is_file() and sha(q)==pin['sha256']
for ext in ('*.olean','*.elf','*.so','*.pyc'): assert not list(p.rglob(ext))
print('PASS: actual source pins, source/import hashes, successful receipt, standard axiom report; no binaries')
