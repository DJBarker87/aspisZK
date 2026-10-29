from pathlib import Path
import json,hashlib,subprocess,base64
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-ownd-20261029';D='/home/dombarker/project-offloads/codex-pv-ownd-20261029'
items=[]
def item(k,p,c):items.append(f'L{{kind:K::{k},producer_row:{p},consumer_row:{c}}}')
for f,t in [(1,2),(2,3),(25,26),(27,28),(28,29),(30,31),(31,32)]:item(f'SpongeCarry{{from:{f},to:{t}}}',f*16+11,t*16)
for k,p,c in [('OwnerOutput',11,28),('NullifierKey',12,412),('InputSaltHead',44,428),('InputSaltTail',60,428)]:item(k,p,c)
for l in range(21):
 a=864+(l//4)*16+1+2*(l%4)
 for k,p,c in [('PrivatePathCurrent',(3+l)*16+11,a),('PrivatePathLeft',a+1,(4+l)*16+12),('PrivatePathRight',a+1,(4+l)*16)]:item(f'{k}{{level:{l}}}',p,c)
for v,p,c in [(0,44,960),(1,460,962),(2,508,964)]:item(f'ValueSource{{value:{v}}}',p,c)
for k,p,c in [('ConservationInput',960,966),('ConservationRecipient',962,966),('ConservationChange',964,967),('ConservationPartial',966,967),('InputSecondCommitment',64,969),('InputSelectedSide',865,969),('OutputSecondCommitment',523,970),('OutputPairFirst',475,540),('OutputPairFirstWithdrawal',523,540),('OutputPairSecond',970,528)]:item(k,p,c)
for l in range(20):
 for k,c in [('AppendCurrentLeft',(34+l)*16+12),('AppendCurrentRight',(34+l)*16)]:item(f'{k}{{level:{l}}}',(33+l)*16+11,c)
assert len(items)==127
s='''use aspis_statement::pool_v1::pair_tree_hiding::{build_pool_v1_pair_copy_row_schedule_v1 as actual,PoolV1PairCopyRowLinkV1 as L,PoolV1PairCopyRowLinkKindV1 as K};
use std::{alloc::{GlobalAlloc,Layout,System},sync::atomic::{AtomicBool,AtomicUsize,Ordering::SeqCst},mem};
static WATCH:AtomicBool=AtomicBool::new(false); static FAIL:AtomicBool=AtomicBool::new(false);
static ALLOCS:AtomicUsize=AtomicUsize::new(0);static FREES:AtomicUsize=AtomicUsize::new(0);static REALLOCS:AtomicUsize=AtomicUsize::new(0);
struct A;#[global_allocator]static ALLOC:A=A;
unsafe impl GlobalAlloc for A{
 unsafe fn alloc(&self,l:Layout)->*mut u8{if WATCH.load(SeqCst){assert_eq!((l.size(),l.align()),(1016,2));ALLOCS.fetch_add(1,SeqCst);if FAIL.load(SeqCst){return std::ptr::null_mut();}} unsafe{System.alloc(l)}}
 unsafe fn dealloc(&self,p:*mut u8,l:Layout){if WATCH.load(SeqCst){assert_eq!((l.size(),l.align()),(1016,2));FREES.fetch_add(1,SeqCst);}unsafe{System.dealloc(p,l)}}
 unsafe fn realloc(&self,p:*mut u8,l:Layout,n:usize)->*mut u8{if WATCH.load(SeqCst){REALLOCS.fetch_add(1,SeqCst);}unsafe{System.realloc(p,l,n)}}
}
const EXPECTED:[L;127]=[ITEMS];
fn kind(k:K)->(u8,Option<u8>,Option<u8>){match k{
 K::SpongeCarry{from,to}=>(0,Some(from),Some(to)),K::OwnerOutput=>(1,None,None),K::NullifierKey=>(2,None,None),K::InputSaltHead=>(3,None,None),K::InputSaltTail=>(4,None,None),
 K::PrivatePathCurrent{level}=>(5,Some(level),None),K::PrivatePathLeft{level}=>(6,Some(level),None),K::PrivatePathRight{level}=>(7,Some(level),None),K::ValueSource{value}=>(8,Some(value),None),
 K::ConservationInput=>(9,None,None),K::ConservationRecipient=>(10,None,None),K::ConservationChange=>(11,None,None),K::ConservationPartial=>(12,None,None),K::InputSecondCommitment=>(13,None,None),K::InputSelectedSide=>(14,None,None),K::OutputSecondCommitment=>(15,None,None),K::OutputPairFirst=>(16,None,None),K::OutputPairFirstWithdrawal=>(17,None,None),K::OutputPairSecond=>(18,None,None),K::AppendCurrentLeft{level}=>(19,Some(level),None),K::AppendCurrentRight{level}=>(20,Some(level),None)}}
fn main(){
 assert_eq!((mem::size_of::<L>(),mem::align_of::<L>()),(8,2));assert!(!mem::needs_drop::<L>());
 assert_eq!((mem::offset_of!(L,producer_row),mem::offset_of!(L,consumer_row),mem::offset_of!(L,kind)),(0,2,4));
 let oom=std::env::args().any(|a|a=="--oom");FAIL.store(oom,SeqCst);WATCH.store(true,SeqCst);
 let v=actual().expect("frozen schedule check");
 assert!(!oom);assert_eq!((v.len(),v.capacity()),(127,127));assert_eq!(v.as_slice(),&EXPECTED);
 let mut active=0;
 for x in &v {let p=x as *const L as *const u8;for (off,b) in x.producer_row.to_le_bytes().into_iter().enumerate(){assert_eq!(unsafe{p.add(off).read()},b);active+=1;}for (off,b) in x.consumer_row.to_le_bytes().into_iter().enumerate(){assert_eq!(unsafe{p.add(2+off).read()},b);active+=1;}let(t,a,b)=kind(x.kind);assert_eq!(unsafe{p.add(4).read()},t);active+=1;if let Some(a)=a{assert_eq!(unsafe{p.add(5).read()},a);active+=1;}if let Some(b)=b{assert_eq!(unsafe{p.add(6).read()},b);active+=1;}}
 assert_eq!((ALLOCS.load(SeqCst),REALLOCS.load(SeqCst),FREES.load(SeqCst)),(1,0,0));drop(v);
 assert_eq!((ALLOCS.load(SeqCst),REALLOCS.load(SeqCst),FREES.load(SeqCst)),(1,0,1));WATCH.store(false,SeqCst);
 println!("127 actual full Links, {active} active bytes; cap127; alloc1016/2 then one free1016/2; no realloc; padding never read; finite validation only");}
'''.replace('ITEMS',',\n'.join(items))
(R/'tools/pv-ownd-20261029/initial.rs').write_text(s)
records=[]
for rel in ['crates/aspis-statement/src/pool_v1/'+f for f in ['pair_tree_hiding.rs','pair_tree_profile.rs','pair_forest_hiding.rs']]:
 b=subprocess.check_output(['git','show','HEAD:'+rel]);records.append(dict(path=rel,host_path='/home/dombarker/project-offloads/codex-pv-fscan-20261028/src/'+rel,sha256=hashlib.sha256(b).hexdigest(),blob=subprocess.check_output(['git','rev-parse','HEAD:'+rel],text=True).strip()))
(E/'native-inputs.json').write_text(json.dumps(dict(sources=records),indent=2)+'\n')
