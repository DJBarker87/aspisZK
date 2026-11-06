from pathlib import Path
import json,hashlib,lzma
B=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=B/'NKU_first_audit/NKU_CLOSURE_PINS.json.xz'
assert sha(p)=='3bc69204295527e54631f756c22936f7580d06d31d290ac194d2096e661a21ab'
old=json.loads(lzma.decompress(p.read_bytes()));new=json.loads(lzma.decompress((B/'NKU_CLOSURE_PINS.json.xz').read_bytes()))
changed=[];same=0
for path,row in old.items():
 assert path in new,('old selected path absent',path)
 assert new[path]['module']==row['module']
 if row['sha256']!=new[path]['sha256']:
  assert row['module']=='NKU_COMBINED_IMPORT',('old dependency changed',row)
  changed.append(path)
 else:same+=1
 assert sha(Path(path))==new[path]['sha256'],('current object drift',path)
assert changed,'combined source set must differ'
export=json.loads((B/'NKU_EXPORT.json').read_text())
for row in export['files']:
 assert sha(Path(row['source']))==row['sha256']==sha(Path(row['path']))
roots=json.loads((B/'NKU_AUDIT_ROOTS.json').read_text());walks=[]
standard={'propext','Classical.choice','Quot.sound'}
for i,group in enumerate(roots['groups']):
 p=B/'NKU_audit'/('batch'+str(i))/('proof'+str(i)+'.json');x=json.loads(p.read_text())
 assert x['exit_status']==0
 assert [r['root'] for r in x['results']]==group
 for r in x['results']:
  assert r['equal'] and set(r['walked_axioms'])==set(r['collect_axioms'])<=standard,r
  reach=B/('NEP_proof'+str(i)+'_'+r['root']+'_REACHABLE.txt');assert reach.is_file()
  walks.append(dict(root=r['root'],receipt=str(p),raw_sha256=sha(reach),reused_from_first_audit=i<13))
assert len(walks)==len(roots['roots']) and len({r['root'] for r in walks})==len(walks)
fixtures=json.loads((B/'NKU_audit/fixtures/fixtures.json').read_text());assert fixtures['exit_status']==0 and len(fixtures['results'])==8
for r in fixtures['results']:
 assert r['equal'] and r['walked_axioms']==r['collect_axioms']
 if r['root'].startswith('NEP_Planted.'):
  assert len(r['walked_axioms'])==1 and r['walked_axioms'][0].startswith('NEP_Planted.')
 else:assert r['walked_axioms']==[]
scan=[json.loads(s) for s in (B/'NKU_LOADED_scan.jsonl').read_text().splitlines()]
assert scan and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
report=dict(pass_all=True,unchanged_old_closure_objects=same,changed_only_combined=changed,export_objects=len(export['files']),roots=len(walks),reused_roots=sum(r['reused_from_first_audit'] for r in walks),new_roots=sum(not r['reused_from_first_audit'] for r in walks),fixtures=8,scan_modules=len(scan),dangling=0,owner_conflicts=0,import_mismatches=0)
(B/'NKU_EXPORT_VERIFY.json').write_text(json.dumps(report,indent=2)+'\n')
(B/'NKU_FINAL_WALK_MANIFEST.json').write_text(json.dumps(dict(source_sets=2,unchanged_dependencies_verified=True,walks=walks),indent=2)+'\n')
print(json.dumps(report))
