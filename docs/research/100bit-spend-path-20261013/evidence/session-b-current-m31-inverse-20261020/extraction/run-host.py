#!/usr/bin/env python3
"""One exact, capped, offline Charon or Aeneas attempt; no Lean invocation."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,signal,subprocess,time
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
TOOLS=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016')
STATIC=Path('/home/dombarker/project-offloads/root-finish-aeneas-combined-v3-20261019/src/_build/default/main.exe')
PINS={
 'charon-target/release/charon':'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8',
 'charon-target/release/charon-driver':'efdbe5b86c9f5f70c93810af08f358d4ecbaecf6f3e87517b1176689a8c28c45',
 'bin/aeneas':'22232f96de983a1cdd4043a3fe2091b3ea4202fdec7a27789ad2612358fb62ae'}
def dump(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True)
 ap.add_argument('--phase',choices=['charon','aeneas'],required=True);ap.add_argument('--attempt',default='a');ap.add_argument('--root-target',choices=['both','verify','prepared'],default='both');a=ap.parse_args()
 w=a.root;kit=w/'input';pins=json.loads((kit/'source-pins.json').read_text())
 for name,h in pins['kit_files'].items():assert sha(kit/name)==h,name
 assert pins['features']==['r0','private-leaf-salts']
 for name,h in PINS.items():assert sha(STATIC if name=='bin/aeneas' else TOOLS/name)==h,name
 cgline=Path('/proc/self/cgroup').read_text().strip();assert cgline.startswith('0::')
 cg=Path('/sys/fs/cgroup')/cgline[3:].lstrip('/')
 limits={n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max']}
 assert limits=={'memory.high':str(512*2**20),'memory.max':str(2*2**30),'memory.swap.max':'0'},limits
 out=w/'runs'/(a.phase+'-'+a.attempt);out.mkdir(parents=True,exist_ok=False);shutil.copytree(kit,out/'input-snapshot')
 llbc=w/'VerifyPreparedPrefix.llbc';gen=w/'generated'
 if a.phase=='charon':
  cmd=[str(TOOLS/'charon-target/release/charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default',
   '--include','core::option::Option','--include','core::result::Result','--include','core::result::_::map_err',
   *sum((['--start-from',p] for p in pins['root_targets']),[]),*sum((['--opaque',path] for path in pins['opaque_paths']),[]),
   '--dest-file',str(llbc),'--','--locked','--offline','--release','--lib','--no-default-features','--features','r0,private-leaf-salts','--jobs','1']
 else:
  prev=json.loads((w/('runs/charon-'+a.attempt+'/receipt.json')).read_text());assert prev['exit_status']==0 and llbc.is_file()
  raw=json.loads(llbc.read_text());assert raw and not raw['has_errors'], 'Rejected invalid LLBC; never pass to Aeneas'
  cmd=[str(STATIC),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisR1M31Inverse','-dest',str(gen),'-subdir','AspisR1M31Inverse','-split-files','-emit-json',str(llbc)]
 env=dict(os.environ);env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(w/'target'),CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true')
 for key in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:env.pop(key,None)
 dump(out/'environment.json',{n:env.get(n) for n in ['PATH','RUSTUP_TOOLCHAIN','CARGO_BUILD_JOBS','CARGO_NET_OFFLINE','CARGO_TARGET_DIR','CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']})
 dump(out/'command.json',cmd)
 before=(cg/'memory.events').read_text();start=time.monotonic();sampled=0;timed_out=False
 with (out/'stdout.log').open('x') as log:
  p=subprocess.Popen(['/usr/bin/time','-v','-o',str(out/'time.log'),*cmd],cwd=kit,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
  while p.poll() is None:
   sampled=max(sampled,int((cg/'memory.current').read_text()))
   if time.monotonic()-start>180:
    timed_out=True;os.killpg(p.pid,signal.SIGTERM)
    try:p.wait(timeout=3)
    except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL)
    break
   time.sleep(.2)
  p.wait()
 timing=(out/'time.log').read_text() if (out/'time.log').exists() else ''
 def number(label):
  m=re.search(re.escape(label)+r':\s*(\d+)',timing);return int(m[1]) if m else None
 outputs={}
 if llbc.is_file():outputs[str(llbc.relative_to(w))]=sha(llbc)
 if gen.exists():
  for f in gen.rglob('*'):
   if f.is_file():outputs[str(f.relative_to(w))]=sha(f)
 receipt={'phase':a.phase,'exit_status':p.returncode,'wall_seconds':time.monotonic()-start,'peak_process_rss_kib':number('Maximum resident set size (kbytes)'),'process_swaps':number('Swaps'),'sampled_cgroup_peak_bytes':sampled,'cgroup_memory_peak_cumulative':int((cg/'memory.peak').read_text()),'cgroup_swap_current':int((cg/'memory.swap.current').read_text()),'memory_events_before':before,'memory_events_after':(cg/'memory.events').read_text(),'limits':limits,'timed_out':timed_out,'source_revision':pins['revision'],'source_pins_sha256':sha(kit/'source-pins.json'),'tool_pins':PINS,'runner_sha256':sha(Path(__file__)),'command':cmd,'outputs':outputs,'root_target':a.root_target,'input_classification':pins.get('classification','ACTUAL unchanged caller bodies with explicit boundaries'),'scope':pins['scope'], 'time_expected':'Compilation and Charon/Aeneas lowering only; no proof generation or arithmetic execution', 'reservation':'Own8GiB plus optional A8GiB <=16GiB <55GiB host safe limit; scope swap0; no C Lean job'}
 dump(out/'receipt.json',receipt);print(json.dumps(receipt),flush=True)
 raise SystemExit(p.returncode)
if __name__=='__main__':main()
