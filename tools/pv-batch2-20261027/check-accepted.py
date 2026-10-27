from pathlib import Path
import hashlib,json,re,subprocess
E=Path('evidence/pv-batch2-20261027');L=Path('docs/research/v8-r0-zk-20261009/lean')
m=json.loads((E/'ACCEPTED-PREFLIGHT.json').read_text());deps={};sources={}
for r in m['kept']:
 p=L/(r['module']+'.lean');assert hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256'],str(p)
 s=p.read_text();assert not re.search(r'^\s*(?:axiom|sorry|admit)\b|\b(?:native_decide|implemented_by|bv_decide)\b',s,re.M),str(p)
 sources[r['module']]=r['source_sha256']
 for name,item in r['dependency_objects'].items():
  path=item['path'];sha=item['sha256']
  if path in deps:assert deps[path]==sha,('dependency changed between focused jobs',path)
  deps[path]=sha
code='''from pathlib import Path
import hashlib,json
x=DEPS
print(json.dumps({p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in x},sort_keys=True))
'''.replace('DEPS',repr(deps))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
now=json.loads(r.stdout);assert now==deps,[(p,deps[p],now.get(p)) for p in deps if deps[p]!=now.get(p)]
# The emitted constructor blocks are preserved verbatim except two static shift types.
rows=json.loads((E/'constructor-split.json').read_text())['modules'];raw=(E/'extraction-weights/generated-252/Funs.lean').read_text().split('namespace PV_B2_252\n',1)[1].rsplit('end PV_B2_252',1)[0]
blocks=[b for b in re.split(r'(?=/-- \[)',raw) if b.strip()]
for row,block in zip(rows,blocks,strict=True):
 assert hashlib.sha256(block.encode()).hexdigest()==row['raw_sha256']
 text=(L/(row['module']+'.lean')).read_text();emitted=text.split('namespace PV_B2_WeightsNative\n',1)[1].split('\n#print axioms')[0]
 assert emitted==block.replace('31#i32','31#u32'),row['module']
r=subprocess.run(['git','diff','--exit-code','5d8dfbebb2','--','crates','programs'],capture_output=True,text=True);assert r.returncode==0,r.stdout+r.stderr
out=dict(check='passed',accepted_sources=sources,dependency_object_hashes=deps,constructor_blocks_checked=len(rows),rust_program_diff_since_resume='empty',forbidden_tokens='none in accepted sources',scope='partial proof closure only; not native original/copy equality or a release manifest')
(E/'ACCEPTED-CHECK.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(check='passed',sources=len(sources),dependency_objects=len(deps),constructor_blocks=len(rows))))
