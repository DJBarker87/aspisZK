#!/usr/bin/env python3
"""Candidate-2 source dispatcher factoring and fixed callback audit.

This is an inverse source-factorization audit, not a Rust interpreter. Lean
checks the universal substitution law for the actual emitted dispatcher.
"""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,tomllib
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
tool=Path(__file__).resolve().parent;repo=tool.parents[4]
candidate='190e1779c3b9530047e4d2dfcdf0022b200d6c35';parent='0330ae7300b3df6602600a727dfd1b969bfbe19a';production='39c2971dd16c95858a4cfd2c9ae35da052eacfa9'
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(rev,path):return subprocess.check_output(['git','-C',str(repo),'show',rev+':'+path])
def item(src,anchor):
 a=src.index(anchor);j=src.index(b'{',a);k=j+1;d=1
 while d:d+=(src[k:k+1]==b'{')-(src[k:k+1]==b'}');k+=1
 return a,k,src[a:k]
assert set(subprocess.check_output(['git','-C',str(repo),'diff','--name-only',parent,candidate],text=True).splitlines())=={'programs/r1-cost-probe/Cargo.toml','programs/r1-cost-probe/src/lib.rs','programs/r1-cost-probe/src/r1_pool_adapter.rs'}
outputs={};owners=[];files=[];vp='crates/aspis-r1-cost-probe/src/verifier.rs';sp='crates/aspis-r1-cost-probe/src/r1_semantic.rs'
anchors={vp:['fn mark(obs:Observer,p:Phase)','pub fn query<','fn query_with_geometry<','pub fn finish_relation(','fn tx1_finish<','fn tx1_prepare<','pub fn tx1<','pub fn tx2<','pub fn tx2_authenticated<'],sp:['fn mark(obs: crate::verifier::Observer,','fn verify_finish<','pub fn verify_observed<']}
allowed={'mark','query_with_geometry','verify_observed','tx1_prepare','tx1_finish','finish_relation','verify_finish'}
for path in [vp,sp]:
 src=read(candidate,path);assert src==read(parent,path),path
 files.append(dict(path=path,candidate_sha256=sha(src),parent_identical=True))
 covered=[]
 for anchor in anchors[path]:
  a,b,raw=item(src,anchor.encode());name=re.search(rb'fn (\w+)',raw)[1].decode();label=('semantic-' if path==sp else 'verifier-')+name
  outputs['fragments/'+label+'.rs']=raw
  uses=[]
  body=raw[raw.index(b'{')+1:-1].decode()
  for match in re.finditer(r'\bobs\b',body):
   pos=match.start();stack=[]
   for n,c in enumerate(body[:pos]):
    if c=='(':stack.append(n)
    elif c==')' and stack:stack.pop()
   enclosing=stack[-1] if stack else None
   callee=re.search(r'([\w:]+)\s*$',body[:enclosing]) if enclosing is not None else None
   callee=callee[1].split('::')[-1] if callee else 'tuple'
   # Dispatcher and semantic marker have separately exact, exhaustive bodies.
   if name!='mark':assert callee in allowed,(path,name,callee,body[max(0,pos-40):pos+40])
   uses.append(dict(body_byte=pos,callee=callee))
  covered.extend(range(a,b));owners.append(dict(path=path,name=name,start_byte=a,end_byte_exclusive=b,sha256=sha(raw),observer_uses=uses,classification='source dispatcher' if name=='mark' and path==vp else 'compiled no-op semantic marker' if name=='mark' else 'dispatcher calls and internal forwarding only'))
 # All observer variable uses in this source must be covered; no escapes into
 # a boundary omitted from the explicit recursive function closure.
 spans=[(x['start_byte'],x['end_byte_exclusive']) for x in owners if x['path']==path]
 for m in re.finditer(rb'\bobs\b',src):assert any(a<=m.start()<b for a,b in spans),(path,m.start())
 # Functional factoring changes only the observer alias and dispatcher body.
 # All computational function/loop/return/error/hash bodies remain byte exact.
 if path==vp:
  oldalias=b'pub type Observer=Option<fn(Phase)>;';newalias=b'pub type Observer=fn(Phase);'
  oldmark=b'fn mark(obs:Observer,p:Phase) { if let Some(f)=obs {f(p);} }'
  newmark=b'fn mark(obs:Observer,p:Phase) { obs(p); }'
  assert src.count(oldalias)==src.count(oldmark)==1
  factored=src.replace(oldalias,newalias,1).replace(oldmark,newmark,1)
  assert factored.replace(newmark,oldmark,1).replace(newalias,oldalias,1)==src
 else:factored=src
 outputs['factored/'+Path(path).name]=factored
 # Production may contain other retained arithmetic deltas, so its transitive
 # observer-use closure is inventoried separately, not declared byte-identical.
 live=read(production,path)
 files[-1]['production_sha256']=sha(live)
 files[-1]['production_observer_lines']=[dict(line=i,text=l) for i,l in enumerate(live.decode().splitlines(),1) if re.search(r'\bobs\b',l)]
libpath='programs/r1-cost-probe/src/lib.rs';adpath='programs/r1-cost-probe/src/r1_pool_adapter.rs'
oldlib=read(parent,libpath);newlib=read(candidate,libpath)
_,_,callback=item(oldlib,b'fn mark(phase:Phase)');assert callback==item(newlib,b'fn mark(phase:Phase)')[2]==item(read(production,libpath),b'fn mark(phase:Phase)')[2]
expected=b'''fn mark(phase:Phase){
    match phase {
        Phase::QueryPart(i,j)=>msg!("r1:query-part:{}:{}",i,j),
        Phase::SemanticPart(i)=>msg!("r1:semantic-part:{}",i),
        Phase::Parsed=>msg!("r1:parsed"),Phase::Semantic=>msg!("r1:semantic"),Phase::Prepare=>msg!("r1:prepare"),
        Phase::CheckpointRead=>msg!("r1:checkpoint-read"),Phase::CheckpointWrite=>msg!("r1:checkpoint-write"),
        Phase::Merkle(i)=>msg!("r1:merkle:{}",i),Phase::Query(i)=>msg!("r1:query:{}",i),
        Phase::Relation=>msg!("r1:relation"),Phase::Final=>msg!("r1:final"),
    }
    sol_log_compute_units();
}'''
assert callback==expected
outputs['fragments/program-mark.rs']=callback
_,_,observer=item(newlib,b'fn observer()');assert observer==b'''fn observer()->verifier::Observer {
    #[cfg(feature="cu-profiling")] {Some(mark)}
    #[cfg(not(feature="cu-profiling"))] {None}
}'''
outputs['fragments/program-observer.rs']=observer
# Exact complete candidate delta: feature + wrapper, three forwarding sites,
# and two diagnostic-only adapter blocks; inverse restores every original byte.
restored=newlib.replace(b'#[cfg(feature="cu-profiling")]\n#[inline(never)]\nfn mark',b'#[inline(never)]\nfn mark',1)
restored=restored.replace(b'#[inline(always)]\n'+observer+b'\n',b'',1)
assert restored.count(b'observer()')==2
restored=restored.replace(b'observer()',b'Some(mark)');assert restored==oldlib
oldad=read(parent,adpath);newad=read(candidate,adpath)
for message in ['r1:pool-adapter-stage1-checkpoint-written','r1:pool-adapter-stage2-begin']:
 block=('    #[cfg(feature="cu-profiling")]\n    {\n    msg!("'+message+'");\n    solana_program::log::sol_log_compute_units();\n    }').encode()
 inner=('    msg!("'+message+'");\n    solana_program::log::sol_log_compute_units();').encode()
 assert newad.count(block)==1;newad=newad.replace(block,inner,1)
assert newad.count(b'super::observer()')==1;newad=newad.replace(b'super::observer()',b'Some(super::mark)',1);assert newad==oldad
oldtoml=read(parent,'programs/r1-cost-probe/Cargo.toml');newtoml=read(candidate,'programs/r1-cost-probe/Cargo.toml')
assert newtoml.replace(b'# Internal phase/CU diagnostics are opt-in; release verification has no observer.\ncu-profiling = []\n',b'',1)==oldtoml
sdkroot=Path.home()/'.cargo/registry/src/index.crates.io-1949cf8c6b5b557f'
msgpath=sdkroot/'solana-msg-2.2.1/src/lib.rs';msg=msgpath.read_bytes();_,_,macro=item(msg,b'macro_rules! msg ')
assert b'$crate::sol_log(&format!($($arg)*))' in macro
outputs['sdk/msg-macro.rs']=macro
entrypath=sdkroot/'solana-program-entrypoint-2.3.0/src/lib.rs';entry=entrypath.read_bytes();_,_,allocator=item(entry,b'unsafe impl std::alloc::GlobalAlloc for BumpAllocator ')
assert b'unsafe fn dealloc(&self, _: *mut u8, _: Layout)' in allocator and b"// I'm a bump allocator, I don't free" in allocator
outputs['sdk/bump-allocator.rs']=allocator
lock=tomllib.loads(read(candidate,'Cargo.lock').decode());packages={p['name']:p for p in lock['package'] if p['name'] in ['solana-msg','solana-program-entrypoint','solana-program']}
result=dict(candidate=candidate,parent=parent,production=production,features=['pool-adapter','private-leaf-salts'],disabled_features=['cu-profiling','detail-phases','prover'],source_files=files,observer_closure=owners,delta_inverse_checked=True,factorization='The complete original recursive closure consumes only the single observer dispatcher. Changing Observer alias and dispatcher definition to an abstract notify function is eta-lifting mark obs. Every other source byte is unchanged. Lean proves equality of the actual dispatcher functions and arbitrary common computational contexts. This is source-factorization admission, not a second Rust interpreter.',fixed_callback=dict(sha256=sha(callback),all_phase_arms_checked=True,diagnostic_effects_per_invocation=2,formatted_arms=['QueryPart','SemanticPart','Merkle','Query'],message_byte_bounds_64bit={'QueryPart':38,'SemanticPart':20,'Merkle':30,'Query':29},message_bound_scope='Decimal unsigned formatting: at most20 digits for64bit usize,3 foru8. These are payload bounds, not claims about allocator capacity/growth.',application_effects='No application event is erased; only the two exact adapter strings and the fixed program mark messages/CU reports. Error logs, set_return_data and emit_result are unchanged.',resource_contract='Sufficient reference compute/stack/heap, standard returning SDK log syscalls, private formatter allocations with no escape. Does not equate resource exhaustion/panic/divergence to success. Formatted allocations use bump allocator and are not freed; total reference heap sufficiency is essential.'),sdk_packages=packages,sdk_sources={'msg':dict(path=str(msgpath),sha256=sha(msg)),'entrypoint':dict(path=str(entrypath),sha256=sha(entry))},kit_files={n:sha(b) for n,b in outputs.items()})
outputs['source-audit.json']=(json.dumps(result,indent=2)+'\n').encode()
for name,raw in outputs.items():
 p=tool/'profiling-source-audit'/name
 if args.check:assert p.read_bytes()==raw,name
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(raw)
print(json.dumps(dict(check=args.check,owners=len(owners),delta_inverse_checked=True,fixed_callback_bound=True,resource_exhaustion_equality_claimed=False)))
