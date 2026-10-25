"""Local identity/receipt helper; never imports or executes receiver source."""
import ast,base64,datetime,hashlib,json,os,platform,resource,shutil,subprocess,sys,time
from pathlib import Path
E=Path(__file__).resolve().parent
ROOT=Path.cwd()
T=ROOT/'tools/prover-rw-20261023/final-native-gate'
V=T/'prospective-data-v3'
def pin(p):
 b=p.read_bytes();return dict(size=len(b),sha256=hashlib.sha256(b).hexdigest())
def save(name,obj):
 with (E/('FinalNativeGateDataAction-'+name+'.json')).open('x') as f:json.dump(obj,f,indent=2,sort_keys=True)
def rev():return subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def check():
 r=json.loads((V/'FinalNativeGate-release-identities.json').read_text())
 pins={str(p.relative_to(ROOT)):pin(p) for p in sorted(V.rglob('*')) if p.is_file()}
 for n,p in r['source_manifest'].items():assert pin(T/n)==p,n
 for n,p in r['transfer_manifest'].items():assert pin(V/'payload'/n)==p,n
 assert pin(V/'FinalNativeGate-data-transfer.py')==r['receiver']==dict(size=644871,sha256='35092a375a438c7ae92cd643d3c9a261f96f7f870b04fc55b17b7a975dd7b0e4')
 assert pin(V/'FinalNativeGate-data-transport.py')==r['transport']
 tree=ast.parse((V/'FinalNativeGate-data-transfer.py').read_text())
 files=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='FILES' for t in n.targets))
 manifest={}
 for n,row in files.items():
  raw=base64.b85decode(row['b85']);assert raw==(V/'payload'/n).read_bytes()
  manifest[n]=dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
 assert manifest==r['transfer_manifest']
 root=hashlib.sha256(json.dumps(manifest,sort_keys=True).encode()).hexdigest()
 assert root==r['transfer_manifest_root']=='938d8ef30be641940233c564301517c322fe0b2170c77ee7c12dc5976307a145'
 return dict(utc=utc(),revision=rev(),v3_pins=pins,maintained_source_pins=r['source_manifest'],transfer_manifest=manifest,transfer_root=root,source_inventory_count=len(manifest),runtime=dict(executable=sys.executable,version=sys.version,platform=platform.platform(),pin=pin(Path(sys.executable).resolve())),historical_source_revision=json.loads((V/'payload/FinalNativeGate-plan.json').read_text())['source_revision'],print_axioms='N/A')
if sys.argv[1]=='pre':save('preflight',check())
elif sys.argv[1]=='run':
 before=check(); prereg=json.loads((E/'FinalNativeGateDataAction-preflight.json').read_text());assert before['v3_pins']==prereg['v3_pins']
 save('launch',dict(utc=utc(),action_revision=rev(),identity=before,main_actions_charged=1,conditional_status_actions=0,argv=['python3','-B','tools/prover-rw-20261023/final-native-gate/prospective-data-v3/FinalNativeGate-data-transport.py']))
 packet=Path(__import__('tempfile').mkdtemp(prefix='FinalNativeGateDataAction-',dir='/private/tmp'))
 start=time.monotonic();peak=0;samples=0
 with (packet/'transport.stdout').open('xb') as out,(packet/'transport.stderr').open('xb') as err:
  child=subprocess.Popen(['python3','-B','tools/prover-rw-20261023/final-native-gate/prospective-data-v3/FinalNativeGate-data-transport.py'],stdout=out,stderr=err)
  while child.poll() is None:
   rows=subprocess.check_output(['/bin/ps','-axo','pid=,ppid=,rss='],text=True)
   procs={int(a):(int(b),int(c)*1024) for line in rows.splitlines() for a,b,c in [line.split()]}
   own={os.getpid()};changed=True
   while changed:
    new={p for p,(parent,rss) in procs.items() if parent in own};changed=bool(new-own);own|=new
   peak=max(peak,sum(procs[p][1] for p in own if p in procs));samples+=1
   time.sleep(.05)
  code=child.wait()
 usage=resource.getrusage(resource.RUSAGE_SELF);children=resource.getrusage(resource.RUSAGE_CHILDREN)
 result=dict(utc=utc(),action_revision=before['revision'],exit=code,wall_seconds=time.monotonic()-start,packet=str(packet),aggregate_peak_rss_bytes_sampled=peak,sample_count=samples,self_peak_rss_bytes=usage.ru_maxrss,children_max_rss_bytes=children.ru_maxrss,swap_self=usage.ru_nswap,swap_children=children.ru_nswap,print_axioms='N/A',post_identity=check())
 save('execution',result)
 for name in ('transport.stdout','transport.stderr'):shutil.copyfile(packet/name,E/('FinalNativeGateDataAction-'+name))
 print(json.dumps(result|{'post_identity':'retained in evidence'}))
