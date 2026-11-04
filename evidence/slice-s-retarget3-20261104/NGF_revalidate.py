"""Execute unchanged predecessor gates; redirect their report writes into NFX only.

Validation code, inputs and return values are unchanged. Profiling records which
predecessor functions actually ran. Child validators are not provers.
"""
from pathlib import Path
import sys,importlib,subprocess,json,hashlib,time,resource,traceback,os
sys.dont_write_bytecode=True
os.environ['PYTHONDONTWRITEBYTECODE']='1'
E=Path(__file__).resolve().parent;R=E.parents[1]
for p in (R/'evidence').iterdir():
 if p.is_dir():sys.path.insert(0,str(p))
os.environ.update(NGF_REPOSITORY_ROOT=str(R),NGF_CHILD_REPORTS=str(E/'NGF_child_reports'),PYTHONPATH=str(E/'NGF_python_sandbox'))
name=sys.argv[1];assert name in ['NFK','NFS','NFJ','NFQ','NEZ','NEN','NET','NFE']
D=E/'NGF_replay_outputs'/name;D.mkdir(parents=True,exist_ok=True)
# These validators sometimes emit regenerated reports. Preserve all input files.
original_open=Path.open
writes=[]
def safe_open(self,mode='r',*a,**kw):
 if any(c in mode for c in 'wax+') and self.is_relative_to(R) and not self.is_relative_to(E):
  dest=D/self.relative_to(R);dest.parent.mkdir(parents=True,exist_ok=True)
  writes.append(str(self.relative_to(R)));return original_open(dest,mode,*a,**kw)
 return original_open(self,mode,*a,**kw)
Path.open=safe_open
calls={};depth=0;seen_codes=set()
def observe(frame,event,arg):
 if event!='call' or frame.f_code in seen_codes:return
 seen_codes.add(frame.f_code)
 filename=frame.f_code.co_filename
 if not filename.startswith(str(R/'evidence')):return
 p=Path(filename)
 if p.is_relative_to(R/'evidence') and p.name.endswith('.py') and ('validate' in p.name or 'certif' in p.name or p.name.endswith('_check.py')):
  k=str(p.relative_to(R))
  if k not in calls:calls[k]=dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),functions=set())
  calls[k]['functions'].add(frame.f_code.co_name)
# Historical aggregate validators explicitly reject later report corpora. Give
# them an actual private Git HEAD with shared immutable objects and a read-only
# historical file overlay. No validator function, Git result or gate is mocked.
if name in ['NEN','NEZ']:
 directory=R/'evidence'/('ledger4-20261102' if name=='NEN' else 'ledger5-20261104')
 pins=json.loads((directory/(name+'_INPUTS.json')).read_text())
 revision=pins.get('revision') or json.loads((directory/(name+'_SCOPE.json')).read_text())['source_revision']
 gitdir=Path('/private/tmp/NGF_pinned_git_'+name);gitdir.mkdir(exist_ok=True)
 subprocess.run(['git','init','--bare',str(gitdir)],check=True,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
 common=Path(subprocess.check_output(['git','rev-parse','--git-common-dir'],cwd=R,text=True).strip());common=(R/common).resolve()
 (gitdir/'objects/info/alternates').write_text(str(common/'objects')+'\n');(gitdir/'HEAD').write_text(revision+'\n')
 index=Path(subprocess.check_output(['git','rev-parse','--git-path','index'],cwd=R,text=True).strip());index=(R/index).resolve()
 import shutil
 shutil.copy2(index,gitdir/'index')
 subprocess.run(['git','--git-dir='+str(gitdir),'config','core.bare','false'],check=True)
 subprocess.run(['git','--git-dir='+str(gitdir),'config','core.worktree',str(R)],check=True)
 os.environ['GIT_DIR']=str(gitdir);os.environ['GIT_WORK_TREE']=str(R)
 # Pin changed materialized historical inputs, stored once, read bytes exactly.
 mapping={};old_read=Path.read_bytes
 for path,pin in {**pins['files'],**pins.get('report_files',{})}.items():
  local=R/path
  if not local.is_file():continue
  raw=old_read(local);oid=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
  if oid==pin['git_blob']:continue
  hist=subprocess.check_output(['git','cat-file','blob',pin['git_blob']],cwd=R)
  dest=E/'NGF_pinned_inputs'/revision/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(hist);mapping[local]=dest
 if name=='NEZ':
  # A private sparse historical filesystem view makes Git's own dirty check
  # observe the same old bytes as Python, with no simulated Git responses.
  view=Path('/private/tmp/NGF_gitview_NEZ');view.mkdir(exist_ok=True)
  subprocess.run(['git','read-tree',revision],check=True)
  tracked=subprocess.check_output(['git','ls-files','-z'])
  subprocess.run(['git','update-index','--skip-worktree','-z','--stdin'],input=tracked,check=True)
  selected=[]
  for path,pin in pins['files'].items():
   dest=view/path;dest.parent.mkdir(parents=True,exist_ok=True)
   source=mapping.get(R/path,R/path)
   if source.is_file():
    data=old_read(source);oid=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest();assert oid==pin['git_blob'],path
    if not dest.exists():os.link(source,dest)
   elif not dest.exists():dest.write_bytes(subprocess.check_output(['git','cat-file','blob',pin['git_blob']]))
   selected.append(path)
  subprocess.run(['git','--git-dir='+str(gitdir),'config','core.worktree',str(view)],check=True)
  os.environ['GIT_WORK_TREE']=str(view)
  subprocess.run(['git','update-index','--no-skip-worktree','-z','--stdin'],input=('\0'.join(selected)+'\0').encode(),check=True)
 Path.read_bytes=lambda p:old_read(mapping.get(p,p))
 (E/('NGF_'+name+'_SNAPSHOT.json')).write_text(json.dumps(dict(revision=revision,private_git=str(gitdir),object_store=str(common/'objects'),read_overlay={str(k.relative_to(R)):str(v.relative_to(R)) for k,v in mapping.items()}),indent=1)+'\n')
start=time.monotonic();rc=0
try:
 sys.setprofile(observe)
 if name=='NFK':
  m=importlib.import_module('NFK_validate')
  # Replay on its own immutable evidence, including the older C3 ruling file.
  # This is a strict byte-pinned read overlay, never a waived validator check.
  import lzma
  prior=json.loads(lzma.open(m.E/'NFK_LEDGER.json.xz').read());read_original=Path.read_bytes;overlay={}
  for path,pin in prior['NFK_inputs'].items():
   if '@' in path:continue
   local=R/path
   if local.exists() and hashlib.sha256(read_original(local)).hexdigest()!=pin['sha256']:
    raw=subprocess.check_output(['git','show',pin['revision']+':'+path],cwd=R);assert hashlib.sha256(raw).hexdigest()==pin['sha256']
    dest=E/'NGF_pinned_inputs'/pin['revision']/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(raw);overlay[local]=dest
  Path.read_bytes=lambda p:read_original(overlay.get(p,p))
  (E/'NGF_NFK_READ_OVERLAY.json').write_text(json.dumps({str(k.relative_to(R)):str(v.relative_to(R)) for k,v in overlay.items()},indent=1)+'\n')
  result=m.build()
  import lzma
  assert json.loads(lzma.open(m.E/'NFK_LEDGER.json.xz').read())==result
  result=dict(coverage=result['NFK_coverage'],slices=result['NFK_slices'])
 elif name=='NFS':result=importlib.import_module('NFS_validate').validate()
 elif name=='NFJ':
  m=importlib.import_module('NFJ_validate');base=m.baseline();packet=m.read(m.E/'NFJ_LEDGER_DELTA.json');out=m.compose(base,packet)
  assert m.certificate(packet['NFJ_certificates'][m.F],base)
  spec=m.read(R/'docs/research/100bit-spend-path-20261013/design/VERTICAL-SLICES-20261029.json')['slices']['S'];rows=[r for r in out['rows'] if r['function'] in spec['functions']]
  assert rows==m.read(m.E/'NFJ_CHECKED_ROWS.json') and all(r['composed_status']=='CLOSED' for r in rows)
  result=dict(rows=len(rows),all_closed=True)
 elif name=='NFQ':
  m=importlib.import_module('NFQ_validate');assert m.check(json.loads((m.E/'NFQ_SLICE_D.json').read_text()),json.loads((m.E/'NFQ_COVERAGE.json').read_text()))
  c=importlib.import_module('NFQ_certify');c.build()
  for n in ['NFQ_CERTIFICATES.json','NFQ_EDGES.json','NFQ_CLOSED.json','NFQ_LEDGER_DELTA.json','NFQ_AUDIT.json']:
   assert json.loads((D/'evidence/slice-d-define-20261104'/n).read_text())==json.loads((m.E/n).read_text()),n
  result=dict(rows=21,functions=16,roots='OPEN')
 elif name=='NEN':
  m=importlib.import_module('NEN_validate');inputs=m.Inputs()
  try:result=m.build(inputs)
  finally:inputs.close()
  assert result==json.loads((m.E/'NEN_LEDGER.json').read_text());result=dict(coverage=result['coverage'])
 elif name=='NFE':result=importlib.import_module('NFE_validate').validate()
 elif name=='NET':result=importlib.import_module('NET_validate').validate(replay=True)
 elif name=='NEZ':
  m=importlib.import_module('NEZ_validate');result=m.build();assert result==m.read(m.E/'NEZ_LEDGER.json');result=dict(coverage=result['coverage'])
except Exception:
 rc=1;result=dict(error=traceback.format_exc());traceback.print_exc()
finally:sys.setprofile(None)
for x in calls.values():x['functions']=sorted(x['functions'])
u=resource.getrusage(resource.RUSAGE_SELF)
receipt=dict(attempt='NGF_REPLAY_'+name,target=name+' unchanged validation chain',command=sys.argv,exit_status=rc,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,swap='Python local audit: ru_nswap='+str(u.ru_nswap),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),print_axioms='N/A Python; predecessor exact axiom receipts checked',called_validators=calls,redirected_report_writes=writes,result=result)
(E/('NGF_REPLAY_'+name+'.json')).write_text(json.dumps(receipt,indent=1)+'\n')
with (E/'NGF_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
print(json.dumps(dict(predecessor=name,exit_status=rc,seconds=receipt['wall_seconds'],result=result)));sys.exit(rc)
