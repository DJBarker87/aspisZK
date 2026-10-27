"""Read-only final source/object/dependency audit; never launches Lean."""
import pathlib,json,subprocess,shlex,hashlib,re,time
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume9'
receipts=[json.load(open(p)) for p in E.glob('receipt-[0-9]*.json')];objects={};sources={};deps={}
for r in sorted(receipts,key=lambda r:r['attempt']):
 for m in r['modules']:
  if not m['accepted']:continue
  objects[m['module']]=m['object_sha256'];sources[m['module']]=m['source']['sha256']
  for d,v in m['dependencies'].items():
   assert v is not None,(r['attempt'],m['module'],d)
   if d in deps:assert deps[d]==v['sha256'],('dependency changed during campaign',d)
   deps[d]=v['sha256']
external=json.load(open(E.parent/'resume7/external-object-manifest.json'))
for row in external:deps[row['module'].replace('/','.')]=row['object_sha256']
script='''import pathlib,json,hashlib,sys,re,os
x=json.load(sys.stdin);p=pathlib.Path('/home/dombarker/project-offloads/codex-pv-reach-20261027/lean');bad=[];checked=0
for kind,rs in [('objects',x['objects']),('dependencies',x['deps']),('sources',x['sources'])]:
 for m,expected in rs.items():
  q=p/('sources' if kind=='sources' else 'objects')/(m.replace('.','/')+('.lean' if kind=='sources' else '.olean'));actual=hashlib.sha256(q.read_bytes()).hexdigest() if q.is_file() else None;checked+=1
  if actual!=expected:bad.append(dict(kind=kind,module=m,path=str(q),expected=expected,actual=actual))
  if kind in ['objects','sources'] and not q.resolve().is_relative_to(p):bad.append(dict(kind='ownership',module=m,path=str(q),resolved_path=str(q.resolve())))
base=pathlib.Path('/home/dombarker/project-offloads');sent={}
for q in [base/'r1-privacy-build-integration-20261019/sent.txt',base/'r1-privacy-build-integration-20261019/evidence/sent.txt',base/'aspis-fs-generic-20261006/evidence/sent.txt']:
 sent[str(q)]=[s for s in q.read_text().splitlines() if re.search(r'(?<![0-9])402[0-9]{2}(?![0-9])',s)] if q.is_file() else None
print(json.dumps(dict(checked=checked,mismatches=bad,sent_table_range_check=sent),indent=2))
'''
for retry in range(11):
 r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(script)],input=json.dumps(dict(objects=objects,sources=sources,deps=deps)),capture_output=True,text=True)
 if r.returncode!=255:break
 with (E/'transport-retries.jsonl').open('a') as f:f.write(json.dumps(dict(operation='final-read-only-cache-check',retry=retry,stderr=r.stderr))+'\n')
 if retry<10:time.sleep(60)
r.check_returncode();d=json.loads(r.stdout);d.update(accepted_compiled_objects=len(objects),accepted_sources=len(sources),dependency_objects=len(deps),external_objects=len(external),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),scope='current exact fingerprints of this campaign; inherited base is not a newly executed release rebuild')
(E/'final-cache-check.json').write_text(json.dumps(d,indent=2)+'\n');print('checked',d['checked'],'mismatches',len(d['mismatches']));assert not d['mismatches']
