from pathlib import Path
import os,json,subprocess,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2c-20261028');OLD=D.parent/'codex-pv-rdb2-20261028';P=D/'weights-fixture';P.mkdir(exist_ok=True)
for f in ['Cargo.toml','Cargo.lock']:(P/f).write_bytes((OLD/'classification-project-fixture'/f).read_bytes())
# Create own fixture; the old shared source directory is read-only and hash-pinned.
m=(P/'Cargo.toml').read_text();m=m[:m.index('[lib]')] if '[lib]' in m else m[:m.index('[[bin]]')]
m+='''[[bin]]
name="fixture"
path="fixture.rs"
[profile.release]
overflow-checks=false
debug-assertions=false
[features]
default=["ct-host-prover"]
ct-host-prover=[]
''';(P/'Cargo.toml').write_text(m)
s='''use aspis_r1_cost_probe::{weights::Weights,transport::Variant};
use aspis_core::{field::{QM31,CM31,M31,WideExact},circle::SecureCirclePoint};
use std::alloc::{GlobalAlloc,Layout,System};
use std::sync::atomic::{AtomicUsize,Ordering};
struct Tracer;
static TRACK:AtomicUsize=AtomicUsize::new(0);
static COUNT:AtomicUsize=AtomicUsize::new(0);
static SIZE:AtomicUsize=AtomicUsize::new(0);
static ALIGN:AtomicUsize=AtomicUsize::new(0);
unsafe impl GlobalAlloc for Tracer {
 unsafe fn alloc(&self,l:Layout)->*mut u8 {if TRACK.load(Ordering::Relaxed)!=0 {COUNT.fetch_add(1,Ordering::Relaxed);SIZE.store(l.size(),Ordering::Relaxed);ALIGN.store(l.align(),Ordering::Relaxed);}System.alloc(l)}
 unsafe fn dealloc(&self,p:*mut u8,l:Layout){System.dealloc(p,l)}
 unsafe fn realloc(&self,p:*mut u8,l:Layout,n:usize)->*mut u8 {if TRACK.load(Ordering::Relaxed)!=0 {panic!("unexpected realloc")}System.realloc(p,l,n)}
}
#[global_allocator]static A:Tracer=Tracer;
fn q(x:u32)->QM31{QM31{c0:CM31{a:M31(x),b:M31(0)},c1:CM31{a:M31(0),b:M31(0)}}}
fn start(){COUNT.store(0,Ordering::Relaxed);TRACK.store(1,Ordering::Relaxed);}
fn stop(size:usize,align:usize){TRACK.store(0,Ordering::Relaxed);assert_eq!(COUNT.load(Ordering::Relaxed),1);assert_eq!(SIZE.load(Ordering::Relaxed),size);assert_eq!(ALIGN.load(Ordering::Relaxed),align);}
fn main(){
 let mut count=0;
 for variant in [Variant::S1,Variant::S2,Variant::D] {for x in [0,1,2,17,2147483646] {
 let a=core::array::from_fn(|i|q((x+i as u32)%2147483647));let z=[SecureCirclePoint{x:q(x),y:q(1)};2];
 start();let w=Weights::new(variant,&a,&z).unwrap();stop(std::mem::size_of::<Weights>(),std::mem::align_of::<Weights>());
 assert_eq!(w.extra,a[8..10]);
 start();let out=w.materialize(WideExact::ONE).unwrap();stop(1024*std::mem::size_of::<WideExact>(),std::mem::align_of::<WideExact>());
 assert_eq!(out.len(),1024);count+=1;
 }}
 println!("finite validation: {count} constructor/materialize request pairs; size Weights={} align={}; WideExact={} align={}; no realloc",std::mem::size_of::<Weights>(),std::mem::align_of::<Weights>(),std::mem::size_of::<WideExact>(),std::mem::align_of::<WideExact>());
}
''';(P/'fixture.rs').write_text(s)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',CARGO_TARGET_DIR=str(D/'target-weights'),CARGO_BUILD_JOBS='4',RUSTC_BOOTSTRAP='1',RUSTFLAGS='-Zdump-mir=box_from_parts -Zdump-mir-dir='+str(D/'box-mir'))
metadata=subprocess.run(['cargo','metadata','--format-version','1','--manifest-path',str(P/'Cargo.toml')],env=env,capture_output=True,text=True);assert metadata.returncode==0,metadata.stderr
j=json.loads(metadata.stdout);nodes={x['id']:x for x in j['resolve']['nodes']};features=[dict(name=x['name'],version=x['version'],id=x['id'],features=nodes[x['id']]['features']) for x in j['packages']]
cmd=['cargo','run','--release','--locked','--manifest-path',str(P/'Cargo.toml'),'-j','4']
(D/'weights-inputs.json').write_text(json.dumps(dict(command=cmd,fixture_sha256=hashlib.sha256(s.encode()).hexdigest(),resolved_features=features,profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',toolchain='1.94.1',allocator_instrumentation='fixture-only GlobalAlloc delegates to System and logs request count/size/alignment; no production allocator identity or outcome theorem claimed',mir_dump='RUSTC_BOOTSTRAP=1 enables diagnostic dump only; no replacement compiler; dump body takes precedence over source matching',expected_phase='optimized compile then 15 finite request traces; no aggregation'),indent=2))
print('expected time: optimized compilation then 15 finite request traces; no elimination',flush=True)
r=subprocess.run(cmd,env=env);assert r.returncode==0
mir=[]
for p in (D/'box-mir').glob('*'):
 raw=p.read_bytes();mir.append(dict(path=str(p),sha256=hashlib.sha256(raw).hexdigest(),size=len(raw)))
(D/'box-mir-manifest.json').write_text(json.dumps(mir,indent=2));print('MIR files',len(mir))
