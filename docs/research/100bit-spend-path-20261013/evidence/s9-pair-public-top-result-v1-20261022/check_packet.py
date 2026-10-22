from pathlib import Path
import hashlib,json,re
p=Path(__file__).resolve().parent; sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
m=json.loads((p/'manifest.json').read_text()); assert m['schema']=='focused-extractor-proof-packet-v1' and m['compiled_objects_included'] is False
assert m['entry']['role']=='audited_main'
e=m['entry'];src=p/e['source'];rec=json.loads((p/e['receipt']).read_text());pre=json.loads((p/e['preflight']).read_text());cmd=json.loads((p/e['command']).read_text());profile=p/e['profile'];log=(p/e['log']).read_text()
assert sha(src)==e['source_sha256']==rec['source_sha256']==pre['source_sha256']
assert sha(profile)==pre['profile_sha256'] and e['direct_imports']==pre['direct_imports']
assert rec==e['launch_metrics'] and rec['exit_status']==0 and rec['process_swaps']==0 and rec['watchdog_abort'] is None and rec['foreign_lean_samples']==[]
assert rec['object_sha256']==e['object_sha256'] and pre['no_dependency_builds'] is True
assert 'LEAN_PATH='+profile.read_text().strip() in cmd['argv'] and '-j1' in cmd['argv'] and cmd['argv'][cmd['argv'].index('-M')+1]=='4400'
for imp in e['direct_imports'].values():
 q=Path(imp['path']);assert q.is_file() and sha(q)==imp['sha256'],imp['path']
for theorem,axioms in e['theorems'].items():
 reports=re.findall("'"+re.escape(theorem)+r"' depends on axioms:\s*\[(.*?)\]",log,re.S);assert len(reports)==1,theorem
 got=set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*',reports[0]));assert got==set(axioms) and got<={'propext','Classical.choice','Quot.sound'}
text=re.sub(r'/\-.*?\-/','',src.read_text(),flags=re.S);text=re.sub(r'--[^\n]*','',text);assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',text)
for ext in ('*.olean','*.ilean','*.pyc','*.so','*.dylib','*.elf'):assert not list(p.rglob(ext)),ext
for line in (p/'SHA256SUMS').read_text().splitlines():
 digest,rel=line.split('  ',1);assert sha(p/rel)==digest,rel
print('PASS: exact source, receipt, preflight, profile/import pins, standard-only axiom report, and source-only contents')
