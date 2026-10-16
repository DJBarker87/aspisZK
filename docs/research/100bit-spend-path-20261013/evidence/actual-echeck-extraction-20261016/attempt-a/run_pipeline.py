#!/usr/bin/env python3
import hashlib,json,os,re,subprocess,sys,time
from pathlib import Path
A=Path(__file__).resolve().parent; K=A/'input'; O=A/'output'; L=A/'logs'; R=A/'receipts'; S=A/'scope-launches'; TARGET=A/'target'
CARGO='/home/dombarker/.cargo/bin/cargo'; RUSTUP='/home/dombarker/.cargo/bin/rustup'; CHARON='/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon'; AENEAS='/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/bin/aeneas'; TOOLCHAIN='nightly-2026-06-01'
LIMITS={'MemoryHigh':'4G','MemoryMax':'6G','MemorySwapMax':'0','TasksMax':'128'}
ENV={**os.environ,'PATH':'/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN':TOOLCHAIN,'CARGO_BUILD_JOBS':'1','CARGO_PROFILE_RELEASE_OPT_LEVEL':'3','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS':'true','RUSTFLAGS':'-C overflow-checks=yes','CARGO_TARGET_DIR':str(TARGET),'CARGO_NET_OFFLINE':'true'}
def sha(p):
 h=hashlib.sha256()
 with open(p,'rb') as f:
  for b in iter(lambda:f.read(1<<20),b''): h.update(b)
 return h.hexdigest()
def preflight():
 subprocess.run(['sha256sum','-c','SHA256SUMS'],cwd=A,check=True,stdout=(A/'sha256-verify.log').open('w'))
 m=json.loads((A/'manifest.json').read_text())
 expected={'input/Cargo.lock':'db242342f5ce596ad432e58671577e700f1d283a1e7448f5416290496106841d','input/Cargo.toml':'b357a39006a40f4da1647b7b2db72e1bf0f5ef405df13796ab6b0d8f7ebcc261','input/src/lib.rs':'d504089bb0385721e6cf8826b494584d0079ce13c196ed5f4223af12c0f4e8e1','input/src/field.rs':'28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea','input/src/field/wide_exact.rs':'6260fa9d179328714e7df59640abb7a76a326e98900993ce7d3da98c6411d10b','input/src/verifier.rs':'eb0cc6b575bec8ec0c45026194ef51c85bfe51092390ff70518322b6cfb30dd6'}
 for rel,h in expected.items():
  if sha(A/rel)!=h: raise SystemExit('input hash mismatch '+rel)
 if sha(CHARON)!='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8' or sha(AENEAS)!='959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3': raise SystemExit('tool hash mismatch')
 rustc=subprocess.check_output([RUSTUP,'run',TOOLCHAIN,'rustc','--version','--verbose'],text=True)
 if '1.98.0-nightly' not in rustc or '14210df0e27ccd7d9e6a05b8085cbd438e4bbc65' not in rustc: raise SystemExit('rustc pin mismatch')
 cargo_meta=subprocess.run([CARGO,'metadata','--manifest-path',str(K/'Cargo.toml'),'--no-deps','--format-version','1','--offline'],cwd=K,env=ENV,check=True,text=True,stdout=subprocess.PIPE).stdout
 (A/'cargo-metadata.json').write_text(cargo_meta+'\n'); (A/'rustc-version.txt').write_text(rustc)
 (A/'preflight.json').write_text(json.dumps({'manifest_sha256':sha(A/'manifest.json'),'sha256sums_sha256':sha(A/'SHA256SUMS'),'all_inputs_pinned':True,'charon_sha256':sha(CHARON),'aeneas_sha256':sha(AENEAS),'rustc':rustc,'cargo_version':subprocess.check_output([CARGO,'-V'],text=True).strip(),'target_dir':str(TARGET),'features_enabled':[],'network':'offline','release_optimized':True,'preflight_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())},indent=2)+'\n')
def inside(name,cmd):
 L.mkdir(exist_ok=True);R.mkdir(exist_ok=True);log=L/(name+'.log'); recp=R/(name+'.json'); t0=time.monotonic(); wall=time.time()
 with log.open('x') as f: p=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=K,env=ENV,stdout=f,stderr=subprocess.STDOUT)
 cg=next((line[3:] for line in Path('/proc/self/cgroup').read_text().splitlines() if line.startswith('0::')),''); cgr=Path('/sys/fs/cgroup')/cg.lstrip('/')
 def rd(x):
  try:return (cgr/x).read_text().strip()
  except:return None
 txt=log.read_text(errors='replace'); mr=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',txt); mw=re.search(r'Elapsed \(wall clock\) time .*?:\s*([0-9:.]+)',txt)
 rec={'stage':name,'command':cmd,'exit_status':p.returncode,'wall_seconds_monotonic':round(time.monotonic()-t0,3),'usr_bin_time_wall':mw.group(1) if mw else None,'peak_process_rss_kib':int(mr.group(1)) if mr else None,'cgroup':cg,'memory_peak_bytes':rd('memory.peak'),'swap_peak_bytes':rd('memory.swap.peak'),'swap_current_bytes':rd('memory.swap.current'),'memory_events':rd('memory.events'),'memory_high':rd('memory.high'),'memory_max':rd('memory.max'),'swap_max':rd('memory.swap.max'),'pids_max':rd('pids.max'),'limits':LIMITS,'time_started_unix':wall,'runner_sha256':sha(Path(__file__)),'input_manifest_sha256':sha(A/'manifest.json')}; recp.write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec),flush=True);sys.exit(p.returncode)
if len(sys.argv)==4 and sys.argv[1]=='inside': inside(sys.argv[2],json.loads(sys.argv[3]));sys.exit()
preflight();O.mkdir(exist_ok=True);S.mkdir(exist_ok=True)
cmds={
'build':[CARGO,'build','--manifest-path',str(K/'Cargo.toml'),'--package','aspis-r1-mask-extraction-probe','--release','--locked','--offline','--lib'],
'charon':[CHARON,'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','crate::verifier::echeck_round1','--dest-file',str(O/'Echeck.llbc'),'--', '--manifest-path',str(K/'Cargo.toml'),'--package','aspis-r1-mask-extraction-probe','--release','--lib','--locked','--offline'],
'aeneas':[AENEAS,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR1SelectedMaskProbe','-dest',str(O/'generated'),'-subdir','AspisR1SelectedMaskProbe','-split-files','-emit-json','-print-unknown-externals','-loops-to-rec',str(O/'Echeck.llbc')]}
for stage,cmd in cmds.items():
 argv=['systemd-run','--user','--scope','--quiet','--unit=aspis-r1-echeck-'+stage+'-20261016']
 for k,v in LIMITS.items():argv+=['--property='+k+'='+v]
 argv += [sys.executable,str(Path(__file__).resolve()),'inside',stage,json.dumps(cmd,separators=(',',':'))]
 launch=subprocess.run(argv,cwd=A,env=ENV,text=True,capture_output=True,timeout=330)
 (S/(stage+'.json')).write_text(json.dumps({'stage':stage,'systemd_run_argv':argv,'exit_status':launch.returncode,'stdout':launch.stdout,'stderr':launch.stderr,'scope_limits':LIMITS},indent=2)+'\n')
 print(launch.stdout,flush=True);print(launch.stderr,flush=True)
 if launch.returncode: raise SystemExit(launch.returncode)
print('ALL_STAGES_EXITED_ZERO',flush=True)
