"""One unchanged pinned gate, one scope, exact source/tool preflight and trace retention."""
from pathlib import Path
import subprocess,json,hashlib,os,time,sys,re,lzma
ROOT=Path('/home/dombarker/project-offloads/codex-pv-k4trace-20261104')
INFRA=ROOT.parent/'codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
SELF=ROOT/'host_run.py'
def write(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def sha(p):return hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
def admit(out,label,amount):
 q=out/(label+'.json')
 with (out/(label+'.log')).open('w') as f:r=subprocess.run(['python3',str(INFRA/'reservation.py'),str(q),'--requested-bytes',str(amount)],stdout=f,stderr=subprocess.STDOUT)
 if not q.exists():return False
 return r.returncode==0 and json.loads(q.read_text()).get('allowed') is True

def check(config,out):
 rows=[]
 for p,want in config['pins'].items():
  q=Path(config['root'])/p;got=sha(q) if q.is_file() else None;rows.append({'path':str(q),'expected':want,'actual':got,'match':got==want})
 tools={}
 for n,d in json.loads((ROOT/'tools.json').read_text())['tools'].items():
  q=Path(d['path']);got=sha(q);tools[n]={'path':str(q),'actual':got,'expected':d['sha256'],'match':got==d['sha256']}
 write(out/'identity.json',{'sources':rows,'tools':tools})
 return all(x['match'] for x in rows) and all(x['match'] for x in tools.values())
def inside(config,out):
 cg=Path('/sys/fs/cgroup'+Path('/proc/self/cgroup').read_text().split('0::')[1].strip())
 limits={k:(cg/k).read_text().strip() for k in ['memory.high','memory.max','memory.swap.max','pids.max']}
 assert list(limits.values())==[str(6*2**30),str(8*2**30),'0','64'],limits
 if not admit(out,'barrier',0):return 78
 if not check(config,out):write(out/'STOP.json',{'reason':'source/tool mismatch before compiler'});return 66
 env=os.environ.copy();env.pop('QUIET_WINDOW_OWNER',None)
 env.update(PATH='/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='4',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(ROOT/'target'),CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG_ASSERTIONS='false',CARGO_PROFILE_DEV_OVERFLOW_CHECKS='false',TMPDIR=str(ROOT/'tmp'))
 # Only evidence-output flags differ: no assertion, bounds, cap, solver or feature change.
 cmd=config['command'].copy();cmd[cmd.index('--output-format')+1]='old';cmd.insert(2,'--verbose');cmd+=['--trace','--json-ui']
 manifest=cmd[cmd.index('--manifest-path')+1];md=['cargo','metadata','--manifest-path',manifest,'--format-version','1','--offline']
 if '--features' in cmd:md+=['--features',cmd[cmd.index('--features')+1]]
 r=subprocess.run(md,cwd=config['cwd'],env=env,capture_output=True);(out/'metadata.json').write_bytes(r.stdout);(out/'metadata.stderr').write_bytes(r.stderr)
 if r.returncode:return r.returncode
 start=time.time();write(out/'STARTED.json',{'epoch':start,'command':cmd,'config':config})
 with (out/'output.log').open('w') as f:r=subprocess.run(['/usr/bin/time','-v','-o',str(out/'time.log'),'timeout',str(config['timeout']),'taskset','--cpu-list','0-3',*cmd],cwd=config['cwd'],env=env,stdout=f,stderr=subprocess.STDOUT)
 wall=time.time()-start;records=[]
 filt=config['command'][config['command'].index('--harness')+1];exact='--exact' in config['command']
 for p in (ROOT/'target').rglob('*.kani-metadata.json'):
  if p.stat().st_mtime<start-2:continue
  d=json.loads(p.read_text())
  for h in d.get('proof_harnesses',[]):
   name=h.get('pretty_name','')
   if (name!=filt if exact else filt not in name):continue
   q=Path(h['goto_file']);rec={'harness':h,'metadata':str(p),'metadata_sha256':sha(p)}
   if q.exists():
    rec['goto_sha256']=sha(q)
    raw=subprocess.run(['/home/dombarker/.kani/kani-0.67.0/bin/cbmc',str(q),'--show-symbol-table','--json-ui'],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    dst='symbols-'+str(len(records))+'.json.xz';(out/dst).write_bytes(lzma.compress(raw.stdout));rec.update(symbols=dst,symbols_raw_sha256=hashlib.sha256(raw.stdout).hexdigest(),symbols_exit=raw.returncode)
   records.append(rec)
 # Retain Kani name maps, metadata and JSON result artifacts for every selected harness.
 for p in (ROOT/'target').rglob('*.json'):
  if p.stat().st_mtime<start-2:continue
  if any(s in p.name for s in ['pretty_name_map','kani-metadata','symtab','results']):
   rel=str(p.relative_to(ROOT/'target')).replace('/','__');(out/(rel+'.xz')).write_bytes(lzma.compress(p.read_bytes()))
 write(out/'symbols-index.json',{'records':records,'inside_same_scope':True})
 txt=(out/'time.log').read_text();metric=lambda k:int(re.search(re.escape(k)+r':\s*(\d+)',txt)[1])
 receipt={'id':config['id'],'credit':config['credit'],'target':cmd,'original':config['original'],'exit_status':r.returncode,'wall_seconds':wall,'peak_rss_kib':metric('Maximum resident set size (kbytes)'),'swap':metric('Swaps'),'source_revision':'670416be996ba5a0e1c5fb6349a7db34f16714d0','source_pin_manifest':'identity.json','limits':limits,'cgroup_peak_bytes':(cg/'memory.peak').read_text().strip(),'cgroup_swap_peak_bytes':(cg/'memory.swap.peak').read_text().strip(),'print_axioms':'N/A: Kani, 0 Lean','profile':{'opt-level':3,'debug-assertions':False,'overflow-checks':False},'symbol_records':len(records),'cwd':config['cwd']}
 write(out/'receipt.json',receipt)
 # Fail closed; a failing positive is returned for immediate human/agent classification.
 return r.returncode
if sys.argv[1]=='inner':
 c=json.loads(sys.argv[2]);sys.exit(inside(c,ROOT/c['id']))
ident=sys.argv[1];assert re.fullmatch(r'K935[0-3][0-9]',ident)
config=next(r for r in json.loads((ROOT/'runs.json').read_text()) if r['id']==ident)
out=ROOT/ident;out.mkdir(exist_ok=True);assert not (out/'STARTED.json').exists(),'already launched'
last=ROOT/'last-launch.json'
if last.exists():
 remaining=json.loads(last.read_text())['epoch']+180-time.time()
 if remaining>0:print(json.dumps({'cooldown_seconds':remaining}));sys.exit(79)
q=ROOT.parent/'QUIET_WINDOW.json';write(out/'quiet-marker.json',{'epoch':time.time(),'marker':q.read_text() if q.exists() else None})
if not admit(out,'admission',8*2**30):sys.exit(78)
if not check(config,out):write(out/'STOP.json',{'reason':'source/tool mismatch before scope'});sys.exit(66)
write(last,{'id':ident,'epoch':time.time()})
cmd=['systemd-run','--user','--scope','--unit','pv-k4trace-'+ident,'-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(SELF),'inner',json.dumps(config)]
write(out/'scope-command.json',cmd)
with (out/'launcher.log').open('w')as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
print(ident,r.returncode,flush=True);sys.exit(r.returncode)
