from audit11 import *
# Read exact pinned binding packets and hash-check their original installed sources.
packets={row:json.loads(git('show',revs['rw']+':evidence/'+folder+'/v'+row+'-source-bindings.json')) for row,folder in [('197','pv-rdcd7-20261102'),('233','pv-rdcd5-20261101'),('236','pv-rdcd5-20261101')]}
paths={}
def walk(x):
 if isinstance(x,dict):
  if str(x.get('path','')).startswith('/home') and x.get('file_sha256'):paths[x['path']]=x['file_sha256']
  for v in x.values():walk(v)
 elif isinstance(x,list):
  for v in x:walk(v)
for x in packets.values():walk(x)
code='import pathlib,json,base64\nps='+repr(list(paths))+'\nprint(json.dumps({p:base64.b64encode(pathlib.Path(p).read_bytes()).decode() for p in ps}))\n'
r=subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 -'],input=code.encode());d=json.loads(r);sources={p:base64.b64decode(v) for p,v in d.items()}
for p,h in paths.items():assert hashlib.sha256(sources[p]).hexdigest()==h,p
(P/'host-native-sources.json.xz').write_bytes(lzma.compress(r));(P/'host-native-sources.json.sha256').write_text(hashlib.sha256(r).hexdigest()+'\n')
body_checks=[]
for row,x in packets.items():
 entries=x.get('library_bindings',[])+x.get('bindings',[])+([x['deployed_body']] if 'deployed_body' in x else [])
 for z in entries:
  if 'body' in z and z.get('path') in sources:
   raw=sources[z['path']].decode();body=z['body'];assert body in raw,(row,z['path'],body[:70]);body_checks.append({'row':row,'path':z['path'],'body_sha256':hashlib.sha256(body.encode()).hexdigest(),'complete_body_found':True})
x=packets['197'];native=git('show',revs['rw']+':'+x['application_file']);assert hashlib.sha256(native).hexdigest()==x['application_sha256']
for z in x['application_bindings']:assert z['body'] in native.decode()
out={'status':'PASS','host_reads':'read-only exact paths; byte hashes equal immutable binding packets','source_hashes':paths,'complete_body_checks':body_checks,'application_source':{'path':x['application_file'],'sha256':x['application_sha256'],'three_complete_bodies_found':True},'stale_reporting_fields':{'V233.pending':'Preparation-only wording is stale; typed inverse/consumed and final receipts78234/78297-99 supersede it.','V236.status':'PREPARATION ONLY and individual uncompiled labels are stale;78240/78297-99 and unchanged final source close the qualified row.'},'evidence_class':'structural argument, not source-to-machine proof; all runtime/physical/compiler boundaries retained'}
(P/'source-binding-audit11.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS',len(paths),'exact native source hashes;',len(body_checks),'complete body spans; 3 application bodies')
