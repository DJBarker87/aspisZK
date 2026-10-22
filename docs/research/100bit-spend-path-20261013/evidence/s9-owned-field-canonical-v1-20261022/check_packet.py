#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
p=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
m=json.loads((p/'manifest.json').read_text()); e=m['entry']
r=json.loads((p/e['receipt']).read_text()); pre=json.loads((p/e['preflight']).read_text()); cmd=json.loads((p/e['command']).read_text()); src=p/e['source']; log=(p/e['log']).read_text()
assert m['schema']=='focused-extractor-proof-packet-v1' and m['compiled_objects_included'] is False
assert r==e['launch_metrics'] and r['exit_status']==0 and r['process_swaps']==0 and r['watchdog_abort'] is None and r['foreign_lean_samples']==[]
assert sha(src)==e['source_sha256']==r['source_sha256']==pre['source_sha256'] and r['object_sha256']==e['object_sha256']
assert pre['source_revision']==r['source_revision_at_launch'] and pre['no_dependency_builds'] is True
assert pre['controller_sha256']==sha(p/'run_focused.py')
assert e['direct_imports']==pre['direct_imports']
assert 'LEAN_PATH='+ (p/e['profile']).read_text().strip() in cmd['argv']
assert '-j1' in cmd['argv'] and cmd['argv'][cmd['argv'].index('-M')+1]=='4400'
for imp in e['direct_imports'].values(): assert Path(imp['path']).is_file() and sha(Path(imp['path']))==imp['sha256']
for theorem,axioms in e['theorems'].items():
 reports=re.findall("'"+re.escape(theorem)+r"' depends on axioms:\s*\[(.*?)\]",log,re.S); assert len(reports)==1
 got=set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*',reports[0])); assert got==set(axioms) and got<={'propext','Classical.choice','Quot.sound'}
text=src.read_text(); uncommented=re.sub(r'/\-.*?\-/','',text,flags=re.S); uncommented=re.sub(r'--[^\n]*','',uncommented)
assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',uncommented)
assert not re.search(r'set_option\s+(max|.*Heartbeats|.*RecDepth)',uncommented)
for ext in ('*.olean','*.elf','*.so','*.pyc'): assert not list(p.rglob(ext))
for packet in m['linked_packets']: assert (p.parent/packet/'README.md').is_file()
print('PASS: exact field canonicality receipt, standard axioms, imported owners, source links, no compiled objects')
