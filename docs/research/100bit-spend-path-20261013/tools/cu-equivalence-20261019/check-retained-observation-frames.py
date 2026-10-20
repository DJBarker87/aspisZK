#!/usr/bin/env python3
"""Source-frame audit supporting, not replacing, component/trace Lean proofs."""
from pathlib import Path
import hashlib,importlib.util,json,re,resource,subprocess,sys,time
start=time.monotonic();tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4];ev=area/'evidence/cu-equivalence-20261019'
def git(*a):return subprocess.check_output(['git','-C',str(repo),*a])
def rev(s):return git('rev-parse',s).decode().strip()
reference=rev('f458169f7');production=rev('39c2971dd');sha=lambda b:hashlib.sha256(b).hexdigest()
spec=importlib.util.spec_from_file_location('source_cut',area/'tools/public-serializer-extraction-kit/extract.py');cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
class Source:
 def __init__(self,b):self.b=b
 def read_bytes(self):return self.b
def item(b,a):return cut.find_item(Source(b),a)[0]
path='crates/aspis-r1-cost-probe/src/verifier.rs';old=git('show',reference+':'+path);new=git('show',production+':'+path)
unchanged={}
for anchor in ['pub struct Prepared','pub struct View','pub fn checkpoint<','pub fn resume<','fn merkle_path<']:
 a=item(old,anchor);b=item(new,anchor);assert a==b,anchor
 unchanged[anchor]=sha(a)
# Every Merkle leaf/path call and conditional preceding the arithmetic kernel is
# literally the same source, including private salt slices and rejection order.
def query_prefix(b):
 q=item(b,'fn query_with_geometry<');return q[q.index(b'    let i=a.next;'):q.index(b'    let dots=')]
assert query_prefix(old)==query_prefix(new)
# Sampling/challenge code before the gamma-table placement is unchanged. The
# serialized Prepared fields and all transcript payloads stay byte identical.
def sample_prefix(b):
 a=b.index(b'        let mut t=Transcript::new(');z=b.index(b'        let rho=t.scalar_k(row+1,&[]);',a)
 return b[a:z+len(b'        let rho=t.scalar_k(row+1,&[]);')]
assert sample_prefix(old)==sample_prefix(new)
# Runtime settlement/account transfers are the same source body; adapter edits
# only replace first with first_decoded and profiling setup/observer selection.
adapter='programs/r1-cost-probe/src/r1_pool_adapter.rs'
a=git('show',reference+':'+adapter);b=git('show',production+':'+adapter)
settlement={}
for anchor in ['fn emit_result(']:
 x=item(a,anchor);y=item(b,anchor);assert x==y;settlement[anchor]=sha(x)
# The deferred-consumer interpretation retains exact immutable producer values:
# query loops change only a/pending; neither Prepared nor gamma scratch is a
# mutable input. This is a source ownership frame, under Rust's existing model.
q=item(new,'fn query_with_geometry<');signature=q[:q.index(b'{')]
assert b'p:&Prepared' in signature and b'g:&[E;29]' in signature
assert b'a:&mut Accumulator' in signature
prepared=item(new,'pub struct Prepared')
assert not any(x in prepared for x in [b'UnsafeCell',b'Cell<',b'RefCell',b'Atomic'])
consumer_frames={}
for anchor in ['pub fn tx2<','pub fn tx2_authenticated<']:
 body=item(new,anchor)
 assert b'let (p,mut a)=resume(' in body and b'let g=powers::<29>(p.gamma);' in body
 assert b'query_with_geometry(&v,&p,&mut a,&g,hash,obs,&geometry,Some(&mut pending))?;' in body
 assert b'finish_relation(&v,&p,&a,obs)' in body
 consumer_frames[anchor]=sha(body)
changed=git('diff','--name-only',reference,production,'--','crates','programs').decode().splitlines()
assert len(changed)==7
pure_changed={}
for leaf in ['fast_dots.rs','fast_pairing.rs','weights.rs']:
 path0='crates/aspis-r1-cost-probe/src/'+leaf
 values={r:git('show',r+':'+path0) for r in [reference,production]}
 for value in values.values():assert not re.search(rb'\b(?:hash|digest|Transcript|merkle)\b',value),path0
 pure_changed[path0]={r:sha(value)for r,value in values.items()}

u=resource.getrusage(resource.RUSAGE_SELF)
r={'status':'RETAINED_OBSERVATION_SOURCE_FRAMES_IDENTICAL','reference':reference,'production':production,'source_path':path,'source_sha256':{'reference':sha(old),'production':sha(new)},'unchanged_items':unchanged,'query_crypto_prefix_sha256':sha(query_prefix(new)),'challenge_schedule_prefix_sha256':sha(sample_prefix(new)),'settlement_items':settlement,'immutable_prepared_and_gamma_query_inputs':True,'resumed_consumer_frames':consumer_frames,'changed_paths':changed,'changed_arithmetic_files_have_no_cryptographic_calls':pure_changed,'scope':'Syntactic source frames only. Arithmetic values, input provenance, loop control, failures and divergence require the selected Lean component/caller proofs. Ordinary Result equality alone is not an oracle trace theorem. The existing expanded_trace_equivalence proves rho query-prefix schedule equality; unchanged cryptographic prefix source, equal inputs and preserved control provide the per-query expansion under the existing source interpretation. No compiled-program or cryptographic security theorem is claimed here.','selected_features':['pool-adapter','private-leaf-salts'],'excluded_features':['prover','cu-profiling'],'audit':{'command':[sys.executable,*sys.argv],'revision':rev('HEAD'),'features':'source observation-frame audit','exit':0,'wall_seconds':time.monotonic()-start,'peak_rss_bytes':u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,'process_swaps':u.ru_nswap,'print_axioms':'N/A: source comparison, not Lean'}}
(ev/'RETAINED-OBSERVATION-FRAMES.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'status':r['status'],'unchanged_items':len(unchanged),'crypto_prefix_identical':True,'challenge_schedule_identical':True,'settlement_identical':True}))
