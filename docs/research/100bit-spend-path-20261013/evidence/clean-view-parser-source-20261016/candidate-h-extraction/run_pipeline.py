#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys,time
from pathlib import Path
A=Path(__file__).resolve().parent; K=A/'input'; O=A/'output'; L=A/'logs'; R=A/'receipts'; S=A/'scope-launches'; TARGET=Path('/home/dombarker/project-offloads/aspis-r1-view-parse-echeck-20261016/shared-target')
CARGO='/home/dombarker/.cargo/bin/cargo'; RUSTUP='/home/dombarker/.cargo/bin/rustup'; CHARON='/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon'; AENEAS='/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/bin/aeneas'; TOOLCHAIN='nightly-2026-06-01'
LIMITS={'MemoryHigh':'4G','MemoryMax':'6G','MemorySwapMax':'0','TasksMax':'128'}
ENV={**os.environ,'PATH':'/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN':TOOLCHAIN,'CARGO_BUILD_JOBS':'1','CARGO_PROFILE_RELEASE_OPT_LEVEL':'3','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':'-C overflow-checks=yes','CARGO_TARGET_DIR':str(TARGET),'CARGO_NET_OFFLINE':'true'}
EXPECTED={'input/Cargo.lock':'d146be04b47b83f4268d02cc7ca8b2b0860748d4ae140fe5f58442d362af3b88','input/Cargo.toml':'8c373290864e999e95bbb131c7644ae8ff32b536aa7579e24afece390bfd3ef0','input/src/lib.rs':'c4e949f5ce1db322c8ea38cca34471f5f67db7f674ebe0992849634ff97533d4','input/src/field.rs':'28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea','input/src/field/wide_exact.rs':'6260fa9d179328714e7df59640abb7a76a326e98900993ce7d3da98c6411d10b','input/src/transport.rs':'11318ff15d5d41e8a5c2a581b400484547c656516d38c8b79812a85ca4f5d3e3','input/src/verifier.rs':'0ff4b1dee86df93934cd4962bfe0e33668bfe08e8335d4044fe446d7e86e1661'}
def sha(p):
 h=hashlib.sha256()
 with open(p,'rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
def preflight():
 for rel,want in EXPECTED.items():
  if sha(A/rel)!=want: raise SystemExit('input pin mismatch '+rel)
 if sha(CHARON)!='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8' or sha(AENEAS)!='959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3':raise SystemExit('tool pin mismatch')
 rustc=subprocess.check_output([RUSTUP,'run',TOOLCHAIN,'rustc','--version','--verbose'],text=True)
 if '1.98.0-nightly' not in rustc or '14210df0e27ccd7d9e6a05b8085cbd438e4bbc65' not in rustc: raise SystemExit('rustc pin mismatch')
 meta=subprocess.run([CARGO,'metadata','--manifest-path',str(K/'Cargo.toml'),'--no-deps','--format-version','1','--offline'],cwd=K,env=ENV,check=True,text=True,stdout=subprocess.PIPE).stdout
 (A/'cargo-metadata.json').write_text(meta+'\n');(A/'rustc-version.txt').write_text(rustc)
 (A/'preflight.json').write_text(json.dumps({'all_inputs_pinned':True,'expected_input_hashes':EXPECTED,'charon_sha256':sha(CHARON),'aeneas_sha256':sha(AENEAS),'rustc':rustc,'cargo_version':subprocess.check_output([CARGO,'-V'],text=True).strip(),'target_dir':str(TARGET),'features_enabled':[],'network':'offline','release_optimized':True,'limits':LIMITS,'preflight_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())},indent=2)+'\n')
def reservation_preflight(stage):
 base=24*1024**3; own=6*1024**3; scopes=[]
 units=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-legend','--plain'],text=True).splitlines()
 for line in units:
  parts=line.split()
  if not parts: continue
  unit=parts[0]
  if unit=='init.scope' or unit.startswith('aspis-r1-viewparse-'): continue
  raw=subprocess.check_output(['systemctl','--user','show','-p','MemoryMax','--value',unit],text=True).strip()
  if raw=='infinity': raise SystemExit('unbounded concurrent scope blocks reservation: '+unit)
  try: cap=int(raw)
  except ValueError: raise SystemExit('unreadable MemoryMax blocks reservation: '+unit+' '+raw)
  scopes.append({'unit':unit,'memory_max_bytes':cap})
 total=base+own+sum(x['memory_max_bytes'] for x in scopes)
 report={'stage':stage,'external_floor_bytes':base,'own_reserved_max_bytes':own,'other_active_scopes':scopes,'aggregate_reserved_max_bytes':total,'aggregate_reserved_max_gib':round(total/1024**3,3),'aggregate_limit_bytes':50*1024**3,'within_limit':total<=50*1024**3,'observed_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())}
 (A/('reservation-'+stage+'.json')).write_text(json.dumps(report,indent=2)+'\n')
 if total>50*1024**3: raise SystemExit('aggregate cap exceeded before '+stage)
def inside(name,cmd):
 L.mkdir(exist_ok=True);R.mkdir(exist_ok=True);log=L/(name+'.log');recp=R/(name+'.json');t0=time.monotonic();wall=time.time()
 with log.open('x') as f:p=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=K,env=ENV,stdout=f,stderr=subprocess.STDOUT)
 cg=next((line[3:] for line in Path('/proc/self/cgroup').read_text().splitlines() if line.startswith('0::')),'');cgr=Path('/sys/fs/cgroup')/cg.lstrip('/')
 def rd(x):
  try:return (cgr/x).read_text().strip()
  except:return None
 txt=log.read_text(errors='replace');mr=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',txt);mw=re.search(r'Elapsed \(wall clock\) time .*?:\s*([0-9:.]+)',txt)
 rec={'stage':name,'command':cmd,'exit_status':p.returncode,'wall_seconds_monotonic':round(time.monotonic()-t0,3),'usr_bin_time_wall':mw.group(1) if mw else None,'peak_process_rss_kib':int(mr.group(1)) if mr else None,'cgroup':cg,'memory_peak_bytes':rd('memory.peak'),'swap_peak_bytes':rd('memory.swap.peak'),'swap_current_bytes':rd('memory.swap.current'),'memory_events':rd('memory.events'),'memory_high':rd('memory.high'),'memory_max':rd('memory.max'),'swap_max':rd('memory.swap.max'),'pids_max':rd('pids.max'),'limits':LIMITS,'time_started_unix':wall,'runner_sha256':sha(Path(__file__))};recp.write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec),flush=True);sys.exit(p.returncode)
if len(sys.argv)==4 and sys.argv[1]=='inside':inside(sys.argv[2],json.loads(sys.argv[3]));sys.exit()
preflight();O.mkdir(exist_ok=True);S.mkdir(exist_ok=True)
cmds={'build':[CARGO,'build','--manifest-path',str(K/'Cargo.toml'),'--package','aspis-r1-view-parse-probe','--release','--locked','--offline','--lib'],'charon':[CHARON,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','crate::verifier::view_parse_probe','--opaque','crate::verifier::query_checks','--dest-file',str(O/'ViewParse.llbc'),'--', '--manifest-path',str(K/'Cargo.toml'),'--package','aspis-r1-view-parse-probe','--release','--lib','--locked','--offline'],'aeneas':[AENEAS,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR1ViewParseProbe','-dest',str(O/'generated'),'-subdir','AspisR1ViewParseProbe','-split-files','-emit-json','-print-unknown-externals','-loops-to-rec',str(O/'ViewParse.llbc')]}
for stage,cmd in cmds.items():
 reservation_preflight(stage)
 argv=['systemd-run','--user','--scope','--quiet','--unit=aspis-r1-viewparse-h-'+stage+'-20261016']
 for k,v in LIMITS.items():argv+=['--property='+k+'='+v]
 argv += [sys.executable,str(Path(__file__).resolve()),'inside',stage,json.dumps(cmd,separators=(',',':'))]
 launch=subprocess.run(argv,cwd=A,env=ENV,text=True,capture_output=True,timeout=330)
 (S/(stage+'.json')).write_text(json.dumps({'stage':stage,'systemd_run_argv':argv,'exit_status':launch.returncode,'stdout':launch.stdout,'stderr':launch.stderr,'scope_limits':LIMITS},indent=2)+'\n');print(launch.stdout,flush=True);print(launch.stderr,flush=True)
 if launch.returncode:raise SystemExit(launch.returncode)
print('ALL_STAGES_EXITED_ZERO',flush=True)
