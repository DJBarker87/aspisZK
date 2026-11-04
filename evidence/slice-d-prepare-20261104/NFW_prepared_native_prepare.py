from pathlib import Path
import json,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;R=E.parents[1];C='crates/aspis-r1-cost-probe/src/';F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
base=subprocess.check_output(['git','show',F+':'+C+'verifier.rs'],cwd=R,text=True)
sig='pub fn new<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,v:&View<\'_>,hash:H,g:&mut [E;29])->Result<Box<Self>,Error> {'
a=base.index(sig);start=base.index('{',a);depth=1;i=start+1
while depth:
 depth+=(base[i]=='{')-(base[i]=='}');i+=1
body=base[start+1:i-1]
newbody=body.replace('Transcript::new(hash,sem.transcript.state(),v.variant)','OracleTranscript::new(hash,sem.transcript.state(),v.variant,ops)').replace('*g=powers::<29>(gamma);','*g=power(gamma,t.ops);').replace('prepared_claim(sem,v.y1,v.inactive,g,kappa)?','claim(sem,v.y1,v.inactive,g,kappa,t.ops)?').replace('Box::new(Self{','Box::new(Prepared{')
code='''use super::*;
use aspis_core::field::CM31;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
#[derive(Clone,Copy)]struct Hash(u8);
impl Digest32 for Hash {fn digest(&self,_:&[&[u8]])->[u8;32]{assert!(false,"unexpected digest outside oracle cut");[0;32]}}
fn any_q()->K{K{c0:CM31{a:M31(kani::any()),b:M31(kani::any())},c1:CM31{a:M31(kani::any()),b:M31(kani::any())}}}
fn any_e()->E{let words:[u32;8]=kani::any();let mut i=0;while i<8{kani::assume(words[i]<2147483647);i+=1;}E::from_limbs(words).unwrap()}
fn es<const N:usize>()->[E;N]{let mut xs=[E::ZERO;N];let mut i=0;while i<N{xs[i]=any_e();i+=1;}xs}
fn qs<const N:usize>()->[K;N]{let mut xs=[K::ZERO;N];let mut i=0;while i<N{xs[i]=any_q();i+=1;}xs}
fn error(code:u8)->Error{match code%8{0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}
fn semantic(hash:Hash)->crate::r1_semantic::Verified<Hash>{
 let c=crate::r1_wire::Challenges{lambda:any_q(),chi:any_q(),theta:any_q(),zc:qs(),mu:any_q(),eta:any_q()};
 crate::r1_semantic::Verified{roots:kani::any(),challenges:c,alpha:qs(),claims:Box::new([qs(),qs(),qs()]),extra:qs(),before_z1:qs(),state_before_z0:kani::any(),z:[SecureCirclePoint{x:any_q(),y:any_q()},SecureCirclePoint{x:any_q(),y:any_q()}],transcript:crate::r1_wire::NFW_wire::seed(hash,kani::any(),kani::any())}
}
struct Ops {states:[[u8;32];7],scalars:[E;4],rho:K,queries:[u32;22],powers:[E;29],claim:E,q_error:bool,c_error:bool,error:Error,
 calls:usize,sc:usize,rows:[u8;6],lens:[usize;6],ptrs:[usize;6],samples:[u8;6],positions:[usize;6],before:[[u8;32];7],before_hash:[u8;6],nonzero:[bool;4],hash:u8,variant:u8,seed:[u8;32],gamma:E,claim_sem:usize,claim_y1:usize,claim_len:usize,claim_inactive:E,claim_kappa:E,claim_g:E,slot:usize}
struct OracleTranscript<'a>{state:[u8;32],hash:Hash,ops:&'a mut Ops}
impl<'a> OracleTranscript<'a>{
 fn new(hash:Hash,seed:[u8;32],variant:Variant,ops:&'a mut Ops)->Self{ops.calls+=1;ops.hash=hash.0;ops.seed=seed;ops.variant=match variant{Variant::S1=>1,Variant::S2=>2,Variant::D=>3};Self{state:ops.states[0],hash,ops}}
 fn record(&mut self,i:usize,row:u8,payload:&[u8]){self.ops.calls+=1;self.ops.rows[i]=row;self.ops.lens[i]=payload.len();self.ops.ptrs[i]=payload.as_ptr() as usize;let at=self.ops.positions[i];self.ops.samples[i]=if at<payload.len(){payload[at]}else{0};self.ops.before[i]=self.state;self.ops.before_hash[i]=self.hash.0;}
 fn scalar(&mut self,row:u8,payload:&[u8],nonzero:bool)->E{let i=self.ops.sc;self.record(i,row,payload);self.ops.nonzero[i]=nonzero;self.ops.sc+=1;self.state=self.ops.states[i+1];self.ops.scalars[i]}
 fn queries(&mut self,row:u8,payload:&[u8])->Result<[u32;22],Error>{self.record(4,row,payload);self.state=self.ops.states[5];if self.ops.q_error{Err(self.ops.error)}else{Ok(self.ops.queries)}}
 fn scalar_k(&mut self,row:u8,payload:&[u8])->K{self.record(5,row,payload);self.state=self.ops.states[6];self.ops.rho}
}
fn power(gamma:E,ops:&mut Ops)->[E;29]{ops.calls+=1;ops.gamma=gamma;ops.powers}
fn claim(sem:&crate::r1_semantic::Verified<Hash>,y1:&[u8],inactive:E,g:&[E;29],kappa:E,ops:&mut Ops)->Result<E,Error>{ops.calls+=1;ops.claim_sem=sem as *const _ as usize;ops.claim_y1=y1.as_ptr() as usize;ops.claim_len=y1.len();ops.claim_inactive=inactive;ops.claim_kappa=kappa;ops.claim_g=g[ops.slot];if ops.c_error{Err(ops.error)}else{Ok(ops.claim)}}
fn new(sem:&crate::r1_semantic::Verified<Hash>,v:&View<'_>,hash:Hash,g:&mut[E;29],ops:&mut Ops)->Result<Box<Prepared>,Error>{
'''+newbody+'''
}
fn ops(slot:usize)->Ops{Ops{states:kani::any(),scalars:es(),rho:any_q(),queries:kani::any(),powers:es(),claim:any_e(),q_error:kani::any(),c_error:kani::any(),error:error(kani::any()),calls:0,sc:0,rows:[0;6],lens:[0;6],ptrs:[0;6],samples:[0;6],positions:kani::any(),before:[[0;32];7],before_hash:[0;6],nonzero:[false;4],hash:0,variant:0,seed:[0;32],gamma:E::ZERO,claim_sem:0,claim_y1:0,claim_len:0,claim_inactive:E::ZERO,claim_kappa:E::ZERO,claim_g:E::ZERO,slot}}
fn check(facet:usize){
 let hash=Hash(kani::any());let sem=semantic(hash);let semantic:[u8;13831]=kani::any();let y1:[u8;928]=kani::any();let round0:[u8;224]=kani::any();let root:[u8;32]=kani::any();let round1:[u8;224]=kani::any();let final_message:[u8;2048]=kani::any();
 let v=View{variant:Variant::S2,semantic:&semantic,y1:&y1,inactive:any_e(),round0:&round0,folded_root:Some(&root),round1:&round1,final_message:&final_message,query_bytes:&[]};
 let slot:usize=kani::any();let word:usize=kani::any();kani::assume(slot<29&&word<8);let mut g=es::<29>();let old=g[slot].to_limbs()[word];let mut o=ops(slot);let result=new(&sem,&v,hash,&mut g,&mut o);
 let good=if o.q_error {matches!(result,Err(e) if e==o.error)&&g[slot].to_limbs()[word]==old&&o.calls==6}
 else if o.c_error {matches!(result,Err(e) if e==o.error)&&g[slot].to_limbs()[word]==o.powers[slot].to_limbs()[word]&&o.calls==9}
 else {result.is_ok()&&o.calls==9};
 if facet==0{assert!(good!=cfg!(NFW_invert));return;}
 if facet==1{if o.q_error{return;}}
 if facet==2{if o.q_error{return;}}
 if facet==1{assert!((o.gamma.to_limbs()[word]==o.scalars[0].to_limbs()[word])!=cfg!(NFW_invert));return;}
 if facet==2{assert!((o.claim_sem==&sem as *const _ as usize&&o.claim_y1==y1.as_ptr() as usize&&o.claim_len==928&&o.claim_inactive.to_limbs()[word]==v.inactive.to_limbs()[word]&&o.claim_kappa.to_limbs()[word]==o.scalars[1].to_limbs()[word]&&o.claim_g.to_limbs()[word]==o.powers[slot].to_limbs()[word])!=cfg!(NFW_invert));return;}
 if facet==3{
  let w:usize=kani::any();kani::assume(w<32);let i:usize=kani::any();kani::assume(i<if o.q_error{5}else{6});
  let seed_ok=o.seed[w]==sem.transcript.state()[w]&&o.hash==hash.0&&o.variant==2;
  let chain=o.before[i][w]==o.states[i][w]&&o.before_hash[i]==hash.0;assert!((seed_ok&&chain)!=cfg!(NFW_invert));return;
 }
 if facet==4{
  let i:usize=kani::any();kani::assume(i<if o.q_error{5}else{6});let at=o.positions[i];let expected=match i{0=>if at<928{y1[at]}else{0},1=>if at<32{v.inactive.to_le_bytes()[at]}else{0},2=>if at<224{round0[at]}else{0},3=>if at<32{root[at]}else if at<256{round1[at-32]}else{0},4=>if at<2048{final_message[at]}else{0},_=>0};
  assert!((o.samples[i]==expected&&o.rows[i]==[27,28,29,30,31,32][i]&&o.lens[i]==[928,32,224,256,2048,0][i])!=cfg!(NFW_invert));return;
 }
 if o.q_error||o.c_error{return;}let p=result.unwrap();
 let value=match facet{5=>p.gamma.to_limbs()[word]==o.scalars[0].to_limbs()[word],6=>p.kappa.to_limbs()[word]==o.scalars[1].to_limbs()[word],7=>{let i:usize=kani::any();kani::assume(i<2);p.alpha[i].to_limbs()[word]==o.scalars[i+2].to_limbs()[word]},8=>{let i:usize=kani::any();kani::assume(i<22);p.queries[i]==o.queries[i]},9=>p.claim.to_limbs()[word]==o.claim.to_limbs()[word],10=>{let i:usize=kani::any();let j:usize=kani::any();kani::assume(i<2&&j<32);p.roots[i][j]==sem.roots[i][j]},11=>{let i:usize=kani::any();kani::assume(i<10);p.semantic_alpha[i]==sem.alpha[i]},12=>{let i:usize=kani::any();kani::assume(i<2);p.z[i]==sem.z[i]},13=>{let i:usize=kani::any();kani::assume(i<32);p.state[i]==o.states[6][i]},_=>p.rho==o.rho};
 assert!(value!=cfg!(NFW_invert));
}
'''
for j in range(15):
 code+='''#[kani::proof] #[kani::unwind(258)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(alloc::vec::Vec::extend_from_slice,KMX_extend_from_slice)]
fn prepared_facet'''+str(j)+'(){check('+str(j)+');}\n'
# A new child module grants no production API; it constructs arbitrary valid
# transcript prestates solely for the caller harness.
wire=subprocess.check_output(['git','show',F+':'+C+'r1_wire.rs'],cwd=R,text=True)
wire+='\n#[cfg(kani)] pub(crate) mod NFW_wire {use super::*;pub(crate) fn seed<H:Digest32>(hash:H,state:[u8;32],next_row:u8)->SemanticTranscript<H>{SemanticTranscript{state,hash,next_row}}}\n'
verifier=base+'\n#[cfg(kani)] #[path="NFW_prepared.rs"] mod NFW_prepared;\n'
files={C+'verifier.rs':verifier,C+'r1_wire.rs':wire,C+'NFW_prepared.rs':code}
x=json.loads((E/'NFW_NATIVE_INPUTS.json').read_text());x.update(files);(E/'NFW_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');x=json.loads((E/'NFW_SOURCE_PINS.json').read_text());x.update({n:hashlib.sha256(t.encode()).hexdigest() for n,t in files.items()});(E/'NFW_SOURCE_PINS.json').write_text(json.dumps(x,indent=1)+'\n')
(E/'NFW_prepared.rs.txt').write_text(code)
patch=''
for n,t in files.items():
 before=subprocess.check_output(['git','show',F+':'+n],cwd=R,text=True) if not n.endswith('NFW_prepared.rs') else ''
 patch+=''.join(difflib.unified_diff(before.splitlines(True),t.splitlines(True),fromfile='a/'+n if before else '/dev/null',tofile='b/'+n))
(E/'NFW_prepared.patch').write_text(patch)
(E/'NFW_PREPARED_NATIVE_SOURCE.json').write_text(json.dumps(dict(source=C+'verifier.rs',frozen_revision=F,signature=sig,original_body=body,transformed_body=newbody,changes=['transcript calls replaced by local record with full typed replies/state','powers/claim cuts take same arguments plus local record','Self output constructor is the identical Prepared type']),indent=1)+'\n')
print('Prepared facets generated',len(code))
