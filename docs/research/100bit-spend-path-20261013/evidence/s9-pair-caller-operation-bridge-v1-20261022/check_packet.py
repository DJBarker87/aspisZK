#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re
p=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
m=json.loads((p/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1' and m['compiled_objects_included'] is False
assert len(m['entries'])==4
for e in m['entries']:
 r=json.loads((p/e['receipt']).read_text());pre=json.loads((p/e['preflight']).read_text());cmd=json.loads((p/e['command']).read_text());log=(p/e['log']).read_text();s=(p/e['source']).read_text()
 assert r==e['launch_metrics'] and r['exit_status']==0 and r['process_swaps']==0 and r['watchdog_abort'] is None and r['foreign_lean_samples']==[]
 assert sha(p/e['source'])==e['source_sha256']==r['source_sha256']==pre['source_sha256'] and r['object_sha256']==e['object_sha256']
 assert pre['source_revision']==r['source_revision_at_launch'] and pre['no_dependency_builds'] is True
 assert pre['controller_sha256']=='9b827933f26ff248491bf1fd187e6d43b804686512bd49b8edacf8ea6416fab0'==sha(p/'run_focused.py')
 assert e['direct_imports']==pre['direct_imports']
 assert 'LEAN_PATH='+(p/e['profile']).read_text().strip() in cmd['argv']
 assert '-j1' in cmd['argv'] and cmd['argv'][cmd['argv'].index('-M')+1]=='4400'
 for imp in e['direct_imports'].values():assert Path(imp['path']).is_file() and sha(Path(imp['path']))==imp['sha256']
 if e['entry_kind']=='audited_main':
  assert len(e['theorems'])==7
  for name,ax in e['theorems'].items():
   reports=re.findall("'"+re.escape(name)+r"' depends on axioms:\s*\[(.*?)\]",log,re.S);assert len(reports)==1,name
   got=set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*',reports[0]));assert got==set(ax) and got<={'propext','Classical.choice','Quot.sound'}
 else:
  assert e['entry_kind']=='compile_only_dependency' and e['theorems']=={} and 'depends on axioms:' not in log
 uncommented=re.sub(r'/\-.*?\-/','',s,flags=re.S);uncommented=re.sub(r'--[^\n]*','',uncommented)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',uncommented)
 assert not re.search(r'set_option\s+(max|.*Heartbeats|.*RecDepth)',uncommented)
# Failed attempts are retained only as diagnostics.
failed=json.loads((p/m['failed_attempts_file']).read_text())
assert {x['attempt'] for x in failed}=={'external-v1','funs-v1','funs-v2'}
for x in failed:
 d=p/x['diagnostic_dir'];rr=json.loads((d/'receipt.json').read_text());assert rr['exit_status']==1 and rr['object_sha256'] is None
 assert rr['source_sha256']==x['source_sha256'] and x['status'].startswith('FAILED')
 assert (d/'lean.log').is_file() and list((d/'sources').glob('*.lean'))
# Key namespace/provenance limitations are explicit.
scope=json.loads((p/m['adapter_scope_file']).read_text())
assert 'globally qualified instDiscriminant' in scope['type_instance_adapter']
assert 'ActualFieldComplete.decodeField' in scope['funs_namespace_adapter']
assert 'fake WideExact' in scope['field_reader_boundary']
assert 'No production caller refinement' in scope['scope']
assert (p/'../s9-candidate-field-decoder-sourcecut-v1-20261022/README.md').resolve().is_file()
for ext in ('*.olean','*.elf','*.so','*.pyc'):assert not list(p.rglob(ext))
for line in (p/'SHA256SUMS').read_text().splitlines():d,rel=line.split('  ',1);assert sha(p/rel)==d,rel
print('PASS: main standard-axiom audit, compile-only adapters, direct object pins, failed diagnostics retained, adapter and provenance limits explicit')
