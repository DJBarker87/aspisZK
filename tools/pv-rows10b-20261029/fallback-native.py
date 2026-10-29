from pathlib import Path
import subprocess,os,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rows10b-20261029');O=D.parent/'codex-pv-ownd-20261029';P=O/'target/release/deps'
S=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/getrandom-0.3.4')
T=D/'fallback-source';(T/'src/backends').mkdir(parents=True,exist_ok=True)
sha=lambda b:hashlib.sha256(b).hexdigest()
append={
'src/lib.rs':r'''
extern crate std;
fn main() {
 assert_eq!(backends::pv_ptr(),0);
 fill(&mut[]).unwrap();
 assert_eq!(backends::pv_ptr(),0);
 let mut cold=[0u8;64];fill(&mut cold).unwrap();
 let initial_ptr=backends::pv_ptr();assert_ne!(initial_ptr,0);
 // Controlled cache prestate selects the original file fallback, without
 // getrandom_test_* cfg or editing any existing source function.
 backends::pv_force_file();
 std::thread::scope(|scope| {
  let mut handles=std::vec::Vec::new();
  for _ in 0..8 {handles.push(scope.spawn(||{let mut b=[0u8;64];fill(&mut b).unwrap();}));}
  for h in handles {h.join().unwrap();}
 });
 let fd=backends::pv_fd();assert!(fd>=0);
 let mut cached=[0u8;64];fill(&mut cached).unwrap();assert_eq!(fd,backends::pv_fd());
 // A controlled external close preserves the stale cache and produces the
 // original read/errno/complete Err branch. It is not an honest-run claim.
 backends::pv_close_cached();
 let mut error=[0u8;64];let e=fill(&mut error).unwrap_err();assert_eq!(e.raw_os_error(),Some(libc::EBADF));
 std::println!("{{\"empty_skips_init\":true,\"cold64_ok\":true,\"concurrent_fallback_calls\":8,\"cached_fd_reused\":true,\"stale_fd_errno\":{},\"getrandom_ptr_selected\":{}}}",e.raw_os_error().unwrap(),initial_ptr!=usize::MAX);
}
''',
'src/backends.rs':r'''
pub(crate) fn pv_ptr()->usize {linux_android_with_fallback::pv_ptr()}
pub(crate) fn pv_force_file(){linux_android_with_fallback::pv_force_file()}
pub(crate) fn pv_fd()->i32 {use_file::pv_fd()}
pub(crate) fn pv_close_cached(){use_file::pv_close_cached()}
''',
'src/backends/linux_android_with_fallback.rs':r'''
pub(super) fn pv_ptr()->usize {GETRANDOM_FN.load(Ordering::Acquire) as usize}
pub(super) fn pv_force_file(){GETRANDOM_FN.store(NOT_AVAILABLE.as_ptr(),Ordering::Release);}
''',
'src/backends/use_file.rs':r'''
pub(super) fn pv_fd()->i32 {FD.load(Ordering::Acquire)}
pub(super) fn pv_close_cached(){let fd=FD.load(Ordering::Acquire);assert!(fd>=0);assert_eq!(unsafe{libc::close(fd)},0);}
'''}
files=['README.md','src/lib.rs','src/error.rs','src/error_std_impls.rs','src/util.rs','src/util_libc.rs','src/backends.rs','src/backends/linux_android_with_fallback.rs','src/backends/use_file.rs','src/backends/sanitizer.rs']
inputs=[]
for f in files:
 b=(S/f).read_bytes();extra=append.get(f,'').encode();p=T/f;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b+extra)
 assert p.read_bytes()[:len(b)]==b
 inputs.append(dict(path=f,original_sha256=sha(b),original_bytes=len(b),harness_sha256=sha(p.read_bytes()),appended_bytes=len(extra),body_change=False))
units=json.loads((O/'deployed-units.json').read_text());u=next(x for x in units if x['package_id'].endswith('#getrandom@0.3.4')and x['target']['name']=='getrandom')
assert u['features']==['std']and u['profile']['opt_level']=='3'and not u['profile']['overflow_checks']and not u['profile']['debug_assertions']
libc=next(P.glob('liblibc-*.rlib'));cfg=next(P.glob('libcfg_if-*.rlib'))
cmd=['rustc','+1.94.1','--edition=2021','-O','-C','debug-assertions=no','-C','overflow-checks=no','-C','panic=unwind','--cfg','feature="std"','--extern','libc='+str(libc),'--extern','cfg_if='+str(cfg),'-L','dependency='+str(P),str(T/'src/lib.rs'),'-o',str(D/'fallback-native')]
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH']);env.pop('LD_PRELOAD',None)
print('Expected time: tiny optimized source-harness compilation/link, then empty/cold/cached and eight concurrent 64-byte file-fallback calls, followed by a controlled stale-FD error',flush=True)
q=subprocess.run(cmd,env=env,text=True,capture_output=True)
print(q.stderr[-4000:],flush=True);q.check_returncode()
q=subprocess.run([str(D/'fallback-native')],env=env,capture_output=True,text=True,check=True,timeout=30);r=json.loads(q.stdout);print(q.stdout,flush=True)
r=dict(command=cmd,toolchain=subprocess.check_output(['rustc','+1.94.1','-Vv'],env=env,text=True),getrandom_unit=u,feature_graph_source=dict(path=str(O/'deployed-units.json'),sha256=sha((O/'deployed-units.json').read_bytes()),all_crates_recorded_in='dispatch-native-result.json#features_all_crates'),inputs=inputs,dependencies=[dict(path=str(p),sha256=sha(p.read_bytes()))for p in [libc,cfg]],binary_sha256=sha((D/'fallback-native').read_bytes()),binary_bytes=(D/'fallback-native').stat().st_size,result=r,evidence_class='finite controlled-cache validation of unchanged deployed-configuration dependency bodies; helper functions appended, no original body edits; not complete own-1 binding',retained='V370, libc syscall identity, actual boundary control publicness; T unchanged')
(D/'fallback-native-result.json').write_text(json.dumps(r,indent=2)+'\n')
