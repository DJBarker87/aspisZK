from pathlib import Path
import subprocess,difflib,json,hashlib
E=Path(__file__).resolve().parent;P='crates/aspis-r1-cost-probe/src/'
frozen=lambda n:subprocess.check_output(['git','show','4bb3b3f:'+n],text=True)
weights=frozen(P+'weights.rs')
def function(n):
 a=weights.index('fn '+n+'(');b=weights.index('{',a);depth=1;i=b+1
 while depth:
  depth+=(weights[i]=='{')-(weights[i]=='}');i+=1
 return weights[a:i]
header=r'''use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn q(x:[u32;4])->K{K{c0:aspis_core::field::CM31{a:M31(x[0]),b:M31(x[1])},c1:aspis_core::field::CM31{a:M31(x[2]),b:M31(x[3])}}}
fn anyk()->K{q(kani::any())}
fn anye()->E{let limbs:[u32;8]=kani::any();for x in limbs{kani::assume(x<0x7fffffff);}E::from_limbs(limbs).unwrap()}
fn err(i:u8)->Error{match i%8{0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}
fn code(e:Error)->u8{match e{Error::Parse=>0,Error::Semantic=>1,Error::Transcript=>2,Error::Relation=>3,Error::Merkle=>4,Error::Query=>5,Error::Checkpoint=>6,Error::Allocation=>7}}
fn reply()->Result<E,Error>{if kani::any(){Ok(anye())}else{Err(err(kani::any()))}}
fn encode(r:Result<E,Error>)->Result<[u32;8],u8>{r.map(|x|x.to_limbs()).map_err(code)}
fn anyweights()->Weights{Weights{variant:Variant::S2,factors:core::array::from_fn(|_|core::array::from_fn(|_|core::array::from_fn(|_|anyk()))),points:core::array::from_fn(|_|core::array::from_fn(|_|anyk())),extra:[anyk(),anyk()]}}
'''
# Exact frozen S2 early-return prefix, without evaluating fallback arithmetic.
dispatch=r'''
struct Dispatch{bytes:*const u8,len:usize,low:*const E,calls:usize,out:E}
fn child(f:&[u8],low:&[E;16],l:&mut Dispatch)->E{l.bytes=f.as_ptr();l.len=f.len();l.low=low.as_ptr();l.calls+=1;l.out}
fn dispatch_cut(weights:&Weights,f:&[u8],low:&[E;16],l:&mut Dispatch)->Option<E>{
 if weights.variant==Variant::S2 && f.len()==64*32 {return Some(child(f,low,l));}None
}
fn dispatch_check(g:usize){
 let w=anyweights();let f:[u8;2048]=[0;2048];let low:[E;16]=core::array::from_fn(|_|anye());
 let mut l=Dispatch{bytes:core::ptr::null(),len:0,low:core::ptr::null(),calls:0,out:anye()};
 let out=dispatch_cut(&w,&f,&low,&mut l);
 if cfg!(NHX_corrupt){match g{0=>l.bytes=l.bytes.wrapping_add(1),1=>l.low=l.low.wrapping_add(1),2=>l.calls+=1,_=>l.out=E::ZERO}}
 let good=match g{0=>l.bytes==f.as_ptr()&&l.len==2048,1=>l.low==low.as_ptr(),2=>l.calls==1,_=>out==Some(l.out)};
 assert!(good);
}
'''
partial=r'''
struct Partial{bytes:*const u8,len:usize,common:*const K,side:usize,calls:usize,out:Result<E,Error>}
fn partial(f:&[u8],common:&[K;16],s:usize,l:&mut Partial)->Result<E,Error>{l.bytes=f.as_ptr();l.len=f.len();l.common=common.as_ptr();l.side=s;l.calls+=1;l.out}
fn partial_window(f:&[u8],common:&[K;16],s:usize,partials:&mut [E;4],l:&mut Partial)->Result<(),Error>{
 partials[s]=partial(f,common,s,l)?;Ok(())
}
fn partial_check(g:usize){
 let f=[0u8;2048];let common=core::array::from_fn(|_|anyk());let before=core::array::from_fn(|_|anye());let mut after=before;
 let s:usize=kani::any();kani::assume(s<4);let j:usize=kani::any();kani::assume(j<4);
 let mut l=Partial{bytes:core::ptr::null(),len:0,common:core::ptr::null(),side:99,calls:0,out:reply()};
 let r=partial_window(&f,&common,s,&mut after,&mut l);
 if cfg!(NHX_corrupt){match g{0=>l.side=4,1=>l.common=l.common.wrapping_add(1),2=>l.calls+=1,_=>after[j]=E::ZERO}}
 let good=match g{
 0=>l.side==s&&l.bytes==f.as_ptr()&&l.len==2048,
 1=>l.common==common.as_ptr(),2=>l.calls==1&&r.map_err(code)==l.out.map(|_|()).map_err(code),
 _=>after[j]==match l.out{Ok(v)if j==s=>v,_=>before[j]}};
 assert!(good);
}
struct Control{calls:usize,sides:[usize;4],stop:usize}
fn control_cut(l:&mut Control)->Result<(),()>{for s in 0..4{l.sides[l.calls]=s;l.calls+=1;if s==l.stop{return Err(())}}Ok(())}
fn partial_control(){let stop:usize=kani::any();kani::assume(stop<=4);let mut l=Control{calls:0,sides:[99;4],stop};let r=control_cut(&mut l);
 if cfg!(NHX_corrupt){l.sides[0]=99;}
 let j:usize=kani::any();kani::assume(j<l.calls);
 assert!(l.calls==if stop<4{stop+1}else{4});assert!(l.sides[j]==j);assert!(r.is_ok()==(stop==4));}
'''
code=header+dispatch+partial+(E/'NHX_producers.rs.txt').read_text()
for fam,count in [('producer',9),('dispatch',4),('partial',4)]:
 for g in range(count):code+=f'''#[kani::proof]#[kani::unwind(2050)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
fn {fam}{g:02}(){{{fam}_check({g});}}\n'''
code+='''#[kani::proof]#[kani::unwind(6)]fn partial_order(){partial_control();}\n'''
inputs={P+'lib.rs':'#![cfg_attr(kani,feature(allocator_api))]\n'+frozen(P+'lib.rs'),P+'weights.rs':weights+'\n#[cfg(kani)] #[path="NHX_parents.rs"] mod NHX_parents;\n',P+'NHX_parents.rs':code}
patch=''
for n,t in inputs.items():
 r=subprocess.run(['git','show','4bb3b3f:'+n],capture_output=True,text=True)
 patch+=''.join(difflib.unified_diff(r.stdout.splitlines(True),t.splitlines(True),fromfile='a/'+n if r.returncode==0 else '/dev/null',tofile='b/'+n))
(E/'NHX_parents.patch').write_text(patch)
# Associations are checked against exact frozen source strings, not names alone.
assert 'if weights.variant==Variant::S2 && f.len()==64*32 {return s2_grouped_inactive_pair(f,low);}'in function('grouped_inactive_pair')
assert 'for s in 0..4 { partials[s]=partial_dot(f,common,s)?; }'in function('shared_partials')
(E/'NHX_PARENT_SOURCE_PINS.json').write_text(json.dumps({n:hashlib.sha256(function(n).encode()).hexdigest() for n in ['grouped_inactive_pair','shared_partials']},indent=2)+'\n')
