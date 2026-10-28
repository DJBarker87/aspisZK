"""Freeze and check the exact V359 native helper; produce finite validation input.
No edits under crates/. No Kani claims. Run from the assigned worktree.
"""
from pathlib import Path
import subprocess, hashlib, json, re
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-l2d-20261028'
p=R/'crates/aspis-r1-cost-probe/src/host_commitment.rs';s=p.read_text()
a=s.index('fn validate_zero_tail(');b=s.index('\nfn opening_lane_values',a)
body=s[a:b].strip()
expected='''fn validate_zero_tail(limbs:&[u32;8],mut i:usize)->Result<(),Error> {
    while i<8 {if limbs[i]!=0 {return Err(Error::WrongField);}i+=1;}
    Ok(())
}'''
flat=lambda s:re.sub(r'\s+','',s)
assert flat(body)==flat(expected),'source changed: review instead of updating expected silently'
# The compiled comparator uses the complete frozen helper byte-for-byte.
harness='''#[derive(Debug, PartialEq)] enum Error { WrongField }
'''+body+'''
#[derive(Debug,PartialEq)] enum Event { Loop(usize,bool), Read(usize), Zero(usize,bool) }
fn instrumented(limbs:&[u32;8],mut i:usize)->(Result<(),Error>,Vec<Event>) {
 let mut t=Vec::new();
 loop {
  t.push(Event::Loop(i,i<8));
  if i>=8 {return (Ok(()),t);}
  t.push(Event::Read(i));t.push(Event::Zero(i,limbs[i]==0));
  if limbs[i]!=0 {return (Err(Error::WrongField),t);}
  i+=1;
 }
}
fn reference(i:usize,xs:&[u32])->(Result<(),Error>,Vec<Event>) {
 match xs.split_first() {
  None=>(Ok(()),vec![Event::Loop(i,false)]),
  Some((&x,rest))=>{
   let mut t=vec![Event::Loop(i,true),Event::Read(i),Event::Zero(i,x==0)];
   if x!=0 {(Err(Error::WrongField),t)} else {
    let (out,trace)=reference(i+1,rest);t.extend(trace);(out,t)
   }
  }
 }
}
fn check(a:[u32;8],first:usize)->usize {
 let native=validate_zero_tail(&a,first);let (out,trace)=instrumented(&a,first);
 assert_eq!(native,out);assert_eq!((out,trace),reference(first,&a[first..]));1
}
fn main(){
 let mut checks=0;
 for mask in 0..256 {
  for x in [1,2,0x7fff_ffff,0xffff_ffff] {
   let a=std::array::from_fn(|i|if mask&(1<<i)!=0 {x} else {0});
   for first in 0..=8 {checks+=check(a,first);}
  }
 }
 let mut state=0x9234_5678_9abc_def0u64;
 for _ in 0..10000 {
  let a=std::array::from_fn(|_| {state^=state<<13;state^=state>>7;state^=state<<17;state as u32});
  for first in [1,4] {checks+=check(a,first);}
 }
 // Nonvacuity: arbitrary in-field limbs pass, first excluded nonzero fails.
 assert_eq!(validate_zero_tail(&[17,0,0,0,0,0,0,0],1),Ok(()));
 assert_eq!(validate_zero_tail(&[19,0,0,0,0,0,0,0],1),Ok(()));
 assert_eq!(validate_zero_tail(&[0,1,0,0,0,0,0,0],1),Err(Error::WrongField));
 println!("{{\\\"checks\\\":{},\\\"failed\\\":0}}",checks);
}
'''
harness=harness.replace(r'\\\"',r'\"')
(R/'tools/pv-l2d-20261028/zero-tail-native.rs').write_text(harness)
(E/'zero-tail-native-source.txt').write_text(body+'\n')
(E/'zero-tail-structural.json').write_text(json.dumps(dict(
 source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 source_path=str(p.relative_to(R)),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),
 body_sha256=hashlib.sha256(body.encode()).hexdigest(),
 frozen_native_body_byte_equal=True,
 evidence_class='structural binding and finite validation preparation; not yet a completed structural (K-1 substitute) native link',
 domain='limbs exactly 8 u32 cells; first <= 8',
 lean_model='PV_L2D_ZeroTail.run first (limbs.drop first)',
 correspondence='index i advances exactly when the current limb is zero; suffix recursion consumes that limb; suffix length is 8-i; final false loop guard at i=8',
 complete_result_law='PV_L2D_ZeroTail.ok_iff; complete_passing; first_bad',
 retained=['array-to-list loop refinement not kernel-proved','honest producer zero-tail association','whole V359 source trace and SAME-cp integration'],
 fidelity='direct read only: no mutable iterator or dropped backward restoration; no Aeneas emission used',
 differential='pending host optimized standalone rustc; no source crate build or feature parity claim'
 ),indent=2)+'\n')
print('frozen native helper and differential written; no native execution')
