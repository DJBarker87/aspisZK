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
name=sys.argv[1];assert name in ['NFK','NFS','NFJ','NFQ','NEZ']
D=E/'NFX_replay_outputs'/name;D.mkdir(parents=True,exist_ok=True)
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
    dest=E/'NFX_pinned_inputs'/pin['revision']/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(raw);overlay[local]=dest
  Path.read_bytes=lambda p:read_original(overlay.get(p,p))
  (E/'NFX_NFK_READ_OVERLAY.json').write_text(json.dumps({str(k.relative_to(R)):str(v.relative_to(R)) for k,v in overlay.items()},indent=1)+'\n')
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
 elif name=='NEZ':
  m=importlib.import_module('NEZ_validate');result=m.build();assert result==m.read(m.E/'NEZ_LEDGER.json');result=dict(coverage=result['coverage'])
except Exception:
 rc=1;result=dict(error=traceback.format_exc());traceback.print_exc()
finally:sys.setprofile(None)
for x in calls.values():x['functions']=sorted(x['functions'])
u=resource.getrusage(resource.RUSAGE_SELF)
receipt=dict(attempt='NFX_REPLAY_'+name,target=name+' unchanged validation chain',command=sys.argv,exit_status=rc,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,swap='Python local audit: ru_nswap='+str(u.ru_nswap),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),print_axioms='N/A Python; predecessor exact axiom receipts checked',called_validators=calls,redirected_report_writes=writes,result=result)
(E/('NFX_REPLAY_'+name+'.json')).write_text(json.dumps(receipt,indent=1)+'\n')
with (E/'NFX_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
print(json.dumps(dict(predecessor=name,exit_status=rc,seconds=receipt['wall_seconds'],result=result)));sys.exit(rc)
