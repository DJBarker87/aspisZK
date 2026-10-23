from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parent
repo=next(p for p in root.parents if (p/'.git').exists())
manifest=json.loads((root/'manifest.json').read_text())
assert manifest['schema']=='focused-extractor-proof-packet-v1'
assert manifest['compiled_objects_included'] is False
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
listed=set()
for f in manifest['files']:
 p=root/f['path']; assert p.is_file() and p.stat().st_size==f['bytes'] and sha(p)==f['sha256'],p
 assert f['path'] not in listed;listed.add(f['path'])
assert listed=={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() and p.name!='manifest.json'}
allowed={'propext','Classical.choice','Quot.sound'}
targets={t['module']:t for t in manifest['targets']};assert len(targets)==15
edges=0
for mod,t in targets.items():
 assert t['exit_status']==0 and t['process_swaps']==0 and t['watchdog_abort'] is None
 assert t['wall_seconds']>0 and t['peak_aggregate_rss_bytes']<8*1024**3 and t['peak_process_rss_bytes']<8*1024**3
 assert t['source_revision_at_launch'] and sha(root/t['source'])==t['source_sha256']
 d=root/'proof'/mod
 rec=json.loads((d/'receipt.json').read_text());pre=json.loads((d/'preflight.json').read_text())
 assert rec['source_sha256']==t['source_sha256'] and rec['object_sha256']==t['object_sha256']
 assert pre['source_sha256']==t['source_sha256'] and pre['limits']['lean_memory_mb']==4400 and pre['limits']['threads']==1
 assert pre['no_dependency_builds'] is True and sha(d/'profile.txt')==pre['profile_sha256']
 imports=re.findall(r'^import (\S+)',(root/t['source']).read_text(),re.M)
 assert set(imports)==set(pre['direct_imports'])
 for imp,pin in pre['direct_imports'].items():
  if imp in targets:
   assert pin['sha256']==targets[imp]['object_sha256'],(mod,imp);edges+=1
 log=(d/'lean.log').read_text();assert 'error:' not in log and 'sorryAx' not in log
 ax=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S)
 assert ax
 assert {n:[a.strip() for a in aa.split(',')] for n,aa in ax}==t['axioms']
 for _,aa in ax:assert {a.strip() for a in aa.split(',')}<=allowed
for ref in manifest['reused_evidence']:assert sha(repo/ref['path'])==ref['sha256']
ownerref=next(x for x in manifest['reused_evidence'] if 'types-funs-named-owner' in x['path'])
owner=json.loads((repo/ownerref['path']).read_text())
for item in owner['coherent_owner_compiles']:
 model=root/'source-model'/Path(item['module']).with_suffix('.lean')
 assert sha(model)==item['source_sha256']
 name=item['module'].replace('/','.')
 for t in targets.values():
  pre=json.loads((root/t['preflight']).read_text())
  if name in pre['direct_imports']:assert pre['direct_imports'][name]['sha256']==item['object_sha256']

for p in root.rglob('*'):
 if p.is_file():assert p.suffix not in {'.olean','.ilean','.ir','.llbc','.pyc','.so','.dylib','.dll','.a','.o'}
print(f'PASS: {len(targets)} focused targets; {edges} included import edges coherent; exact source/receipt/profile pins; standard axioms; source only. S9/security still OPEN.')
