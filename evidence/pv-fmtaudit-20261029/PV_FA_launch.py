from pathlib import Path
import sys,json,hashlib,os,re
from run import run,H
kind=sys.argv[1];id=int(sys.argv[2]);assert 73700<=id<=73799
# Cross-job receipt/sent ID check before launch.
for base,dirs,files in os.walk(H.parent):
 if Path(base)==H:dirs[:]=[];continue
 if len(Path(base).relative_to(H.parent).parts)>=5:dirs[:]=[]
 dirs[:]=[d for d in dirs if d not in {'target','sbf-target','charon-target','node_modules','.git','source','sources','.lake','objects','lean-objects','lean','generated','src','rebuild-objects'}]
 for name in dirs+files:assert not re.search(r'(?<![A-Za-z0-9])'+str(id)+r'(?![A-Za-z0-9])',name),('ID collision',base,name)
 for name in files:
  if name=='sent.txt':assert not any(len(f:=l.split())>2 and f[2]==str(id)for l in(Path(base)/name).read_text().splitlines())
if kind in ['inventory','source','claim_inventory','find_claim_objects','fmt_physical','receipt_find','post','resume_provenance','receiptcheck','resume_prepare']:cmd=['python3',str(H/('PV_FA_'+kind+'.py'))]
elif kind=='pincompile':
 module=sys.argv[3];assert module.startswith(('Aeneas/','AeneasMeta/'));src=H/'pinned-source/backends/lean'/(module+'.lean');sha=hashlib.sha256(src.read_bytes()).hexdigest();cohort='pinned';
 for q in H.glob('pincompile-*/receipt/receipt.json'):
  r=json.loads(q.read_text());assert not(r['exit_status']!=0 and r.get('source_sha256')==sha),'unchanged failed source'
 env=json.loads((H/'pinned.json').read_text());os.environ.update({k:str(v)for k,v in env.items()if v is not None});
 cmd=['timeout','900','python3',str(H/'PV_FA_pinexec.py'),str(id),module]
elif kind=='lean':
 cohort=sys.argv[3];src=H/sys.argv[4];sha=hashlib.sha256(src.read_bytes()).hexdigest()
 for q in H.glob('lean-*/receipt/receipt.json'):
  r=json.loads(q.read_text());assert not(r['exit_status']!=0 and r.get('source_sha256')==sha and r.get('cohort')==cohort),'unchanged failed input'
 assert(H/'resolution.json').exists()
 env=json.loads((H/(cohort+'.json')).read_text());
 cmd=['timeout','900',env['LEAN'],'-M7000','-j1','-DElab.async=false',str(src)]
 os.environ.update({k:str(v)for k,v in env.items()if v is not None})
else:raise Exception(kind)
# run() constructs child environment; preserve the selected Lean env explicitly.
extra={k:v for k,v in os.environ.items()if k.startswith(('LEAN','ELAN','LD_LIBRARY'))}
rc=run(kind+'-'+str(id),cmd,'read-only object provenance inspection; no cohort outputs',extra)
for q in H.glob(kind+'-'+str(id)+'*/receipt/receipt.json'):
 r=json.loads(q.read_text());r.update(attempt=id,kind=kind,launcher_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),inspection_inputs={f:hashlib.sha256((H/f).read_bytes()).hexdigest()for f in ['object-pairs.tsv','footprint-inputs.tsv']if(H/f).exists()})
 if kind in ['lean','pincompile']:
  r.update(cohort=cohort,source_sha256=sha);log=(q.parent/'stdout.log').read_text()+'\n'+(q.parent/'stderr.log').read_text();r['print_axioms']=re.findall(r"^.*(?:depends on axioms|does not depend on any axioms).*",log,re.M)
 q.write_text(json.dumps(r,indent=2))
print('PV_FA_EXIT',rc);sys.exit(rc)
