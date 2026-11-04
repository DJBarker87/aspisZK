from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent;x=json.loads((E/'NGC_NATIVE_INPUTS.json').read_text());n='crates/aspis-r1-cost-probe/src/NGC_windows.rs';s=x[n]
frozen=subprocess.check_output(['git','show','4bb3b3f:crates/aspis-r1-cost-probe/src/verifier.rs'],text=True)
def body(src,signature):
 p=src.index('{',src.index(signature));i=p+1;depth=1
 while depth:depth+=(src[i]=='{')-(src[i]=='}');i+=1
 return src[p+1:i-1]
b=body(frozen,'pub fn checkpoint<')
b=b.replace('let mut out=Vec::with_capacity(checkpoint_size(p.variant));','let mut out=Recorder::new(checkpoint_size(p.variant),selected);')
b=b.replace('hash.digest(&[proof])','digest_control(0,proof.len(),out.count,digests)').replace('hash.digest(&[public])','digest_control(1,public.len(),out.count,digests)')
b=b.replace('hash.digest(&[b"UNPROVED:R1:checkpoint",&out])','digest_control(2,out.len(),out.count,digests)')
b=b.replace('put(&mut out,','put_control(&mut out,').replace('put_k(&mut out,','put_k_control(&mut out,')
s+='''
struct Recorder{cap:usize,len:usize,count:usize,selected:usize,offset:usize,width:usize}
impl Recorder{fn new(cap:usize,selected:usize)->Self{Self{cap,len:0,count:0,selected,offset:9999,width:9999}}fn len(&self)->usize{self.len}fn extend_from_slice(&mut self,piece:&[u8]){if self.count==self.selected{self.offset=self.len;self.width=piece.len();}self.len+=piece.len();self.count+=1;assert!(self.len<=self.cap);}}
struct DigestControl{count:usize,kind:[u8;3],length:[usize;3],at:[usize;3]}
fn digest_control(kind:u8,len:usize,at:usize,log:&mut DigestControl)->[u8;32]{let i=log.count;log.kind[i]=kind;log.length[i]=len;log.at[i]=at;log.count+=1;[0;32]}
fn put_control(out:&mut Recorder,_x:E){out.extend_from_slice(&[0;32]);}
fn put_k_control(out:&mut Recorder,_x:K){out.extend_from_slice(&[0;16]);}
fn checkpoint_control(p:&Prepared,a:&Accumulator,proof:&[u8],public:&[u8],selected:usize,digests:&mut DigestControl)->Recorder{BODY}
fn expected_offset(i:usize)->(usize,usize){if i==0{(0,8)}else if i==1{(8,8)}else if i<11{(16+32*(i-2),32)}else if i==11{(304,16)}else if i<34{(320+4*(i-12),4)}else if i<44{(408+16*(i-34),16)}else if i<48{(568+16*(i-44),16)}else if i<50{(632+32*(i-48),32)}else if i==50{(696,16)}else if i<115{(712+16*(i-51),16)}else{(1736,32)}}
#[kani::proof] KMXL
fn checkpoint_order(){let p=Prepared{variant:Variant::S2,roots:[[0;32];2],gamma:E::ZERO,kappa:E::ZERO,alpha:[E::ZERO;2],rho:K::ZERO,queries:[0;22],semantic_alpha:[K::ZERO;10],z:[SecureCirclePoint{x:K::ZERO,y:K::ZERO};2],claim:E::ZERO,state:[0;32]};let a=Accumulator{weights:oracle_vec(64,K::ZERO,0),rhs:E::ZERO,power:K::ONE,next:10};let selected:usize=kani::any();kani::assume(selected<116);let mut log=DigestControl{count:0,kind:[99;3],length:[99;3],at:[99;3]};let out=checkpoint_control(&p,&a,&[0;57607],&[0;1880],selected,&mut log);let(offset,width)=expected_offset(selected);let exact=out.cap==1768&&out.len==1768&&out.count==116&&out.offset==offset&&out.width==width&&log.count==3&&log.kind==[0,1,2]&&log.length==[57607,1880,1736]&&log.at==[2,3,115];assert!(exact!=cfg!(NGC_invert));}
'''.replace('BODY',b).replace('KMXL','''#[kani::unwind(120)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]''')
x[n]=s;(E/'NGC_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');p=json.loads((E/'NGC_SOURCE_PINS.json').read_text());p.update({n:hashlib.sha256(s.encode()).hexdigest()for n,s in x.items()});(E/'NGC_SOURCE_PINS.json').write_text(json.dumps(p,indent=1)+'\n')
(E/'NGC_CHECKPOINT_CONTROL_SOURCE.json').write_text(json.dumps(dict(frozen_body_sha256=hashlib.sha256(body(frozen,'pub fn checkpoint<').encode()).hexdigest(),control_body_sha256=hashlib.sha256(b.encode()).hexdigest(),method='ruling (ad): source control only; std Vec and byte values replaced by Recorder; chronological syscall-call positions/lengths retained; no value credit from this probe'),indent=1)+'\n')
