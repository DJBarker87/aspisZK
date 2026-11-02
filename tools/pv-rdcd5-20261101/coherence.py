"""Capped final source/object/cohort validation; no compiler or native replay."""
from pathlib import Path
import hashlib,json,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd5-20261101')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
i=json.load(open(D/'coherence-inputs.json'));e=json.load(open(D/'env-J.json'));roots=[Path(x) for x in e['LEAN_PATH'].split(':')]
def obj(m):
 root=next((r for r in roots if (r/m.split('/')[0]).is_dir()),None)
 assert root,('unresolved namespace',m)
 p=root/(m+'.olean');assert p.is_file(),('missing effective object',m,str(p));return p
ext=json.load(open(D/'external-object-manifest.json'))
assert len(ext)==5673
for x in ext:assert sha(obj(x['module']))==x['object_sha256'],x['module']
result={}
pre=json.load(open(D/'preflight-result.json'));success={v['receipt']['module']:v['receipt'] for v in i['launches'].values()}
for m,x in i['modules'].items():
 source=D/'lean-sources'/(m+'.lean');assert sha(source)==x['sha256'],m
 p=obj(m);assert p==D/'lean-objects'/(m+'.olean'),m
 assert m in success or m in pre['reused'],('no accepted source/object receipt',m)
 if m in pre['reused']:assert sha(p)==pre['reused'][m]['object_sha256']
 result[m]=dict(source_sha256=x['sha256'],object_sha256=sha(p),object_path=str(p),imports=[])
 for dep in re.findall(r'^import\s+(\S+)',source.read_text(),re.M):
  dep=dep.replace('.','/');q=obj(dep);result[m]['imports'].append(dict(module=dep,path=str(q),sha256=sha(q)))
for attempt,x in i['launches'].items():
 for m,v in x['dependencies']['objects'].items():assert sha(obj(m))==v['object_sha256'],('launch import changed',attempt,m)
for m,x in pre['reused'].items():
 for dep,pin in x['original_record']['recorded']['imports'].items():assert sha(obj(dep.replace('.','/')))==pin['sha256'],('reuse import changed',m,dep)
for x in i['native_source_pins']:assert sha(Path(x['path']))==x['sha256'],x['path']
(D/'coherence-result.json').write_text(json.dumps(dict(revision=i['revision'],external_count=len(ext),external_manifest_sha256=sha(D/'external-object-manifest.json'),modules=result,launches=len(i['launches']),native_source_pins=len(i['native_source_pins']),environment=e,status='PASS: effective first-namespace paths, source/object hashes, every actual-launch import, reused cohort and native source pins'),indent=2)+'\n')
print('Coherence PASS:',len(result),'project objects;',len(ext),'external objects;',len(i['launches']),'launch snapshots')
