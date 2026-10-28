from pathlib import Path
import difflib,re,json
E=Path(__file__).resolve().parent
s=Path('/tmp/NBZ_windows.rs').read_text().replace('//!','//')
s=s[:s.index('fn NBZ_window<')]
# Reuse the exact inherited field replacement; no field arithmetic is verified anew.
p=(E.parent/'native-query2-20261027/NBF_harness.patch').read_text()
p='\n'.join(l[1:] for l in p.splitlines() if l.startswith('+') and not l.startswith('+++'))
a=p.index('mod NBF_field {');b=a;d=0;opened=False
while b<len(p):
 if p[b]=='{':d+=1;opened=True
 if p[b]=='}':d-=1
 b+=1
 if opened and d==0:break
s+=p[a:b].replace('NBF_field','NBZ_field')+'\n'
s+='''
fn NBZ_e()->E {let w:[u32;8]=kani::any();for x in w {kani::assume(x<2147483647);}E::from_limbs(w).unwrap()}
// One literal inner Horner call from both frozen fold bodies.
fn NBZ_horner_expression(alpha:E,h:E,previous:E)->E {h.add(alpha.mul(previous))}
fn NBZ_horner_case(negative:bool){
 let alpha=NBZ_e();let h=NBZ_e();let previous=NBZ_e();let k:usize=kani::any();kani::assume(k<8);
 let out=NBZ_horner_expression(alpha,h,previous);
 unsafe {
  assert_eq!(NBZ_field::WC,1);assert_eq!(NBZ_field::WX[0][k],alpha.to_limbs()[k]);assert_eq!(NBZ_field::WY[0][k],previous.to_limbs()[k]);
  let z=E::from_limbs(NBZ_field::WO[0]).unwrap();let expected=h.add(z).to_limbs()[k];
  if negative{assert_ne!(out.to_limbs()[k],expected);}else{assert_eq!(out.to_limbs()[k],expected);}
  assert!(out.to_limbs()[k]<2147483647);
 }
 kani::cover!(k==0);kani::cover!(k==7);
}
// One U64 word within an actual full 64-row Vec, arbitrary allocation capacity.
fn NBZ_raw_word_case(negative:bool) {
 let cap=NBZ_cap::<[u64;4]>(64);let mut raw=NBZ_raw(cap);let ptr=raw.as_ptr();
 let i:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();let l:usize=kani::any();
 kani::assume(i<64&&j<64&&k<4&&l<4);let before=raw[j][l];let reply:u64=kani::any();
 raw[i][k..k+1].copy_from_slice(&[reply]);
 let expected=if i==j&&k==l{reply}else{before};
 if negative{assert_ne!(raw[j][l],expected);}else{assert_eq!(raw[j][l],expected);}
 assert_eq!(raw.as_ptr(),ptr);assert_eq!(raw.len(),64);assert_eq!(raw.capacity(),cap);
 kani::cover!(i==63&&k==3);kani::cover!(i!=j);kani::cover!(i==j&&k!=l);kani::cover!(cap>64);
}
static mut NBZ_RIN:[u64;4]=[0;4];static mut NBZ_ROUT:[u32;4]=[0;4];static mut NBZ_RCALLS:usize=0;
fn NBZ_reducer(x:u64)->M31 {unsafe{let i=NBZ_RCALLS;assert!(i<4);NBZ_RCALLS+=1;assert_eq!(x,NBZ_RIN[i]);M31(NBZ_ROUT[i])}}
fn NBZ_finish_case(negative:bool) {
 let rc=NBZ_cap::<[u64;4]>(64);let wc=NBZ_cap::<K>(64);
 let b=BatchedWeights{raw:NBZ_raw(rc),terms:kani::any()};let mut out=NBZ_weights(wc);
 let i:usize=kani::any();kani::assume(i<=64);let j:usize=kani::any();kani::assume(j<64);let k:usize=kani::any();kani::assume(k<4);
 let before=NBZ_qwords(out[j])[k];let optr=out.as_ptr();let bptr=b.raw.as_ptr();let oldterms=b.terms;
 let reply:[u32;4]=kani::any();for x in reply{kani::assume(x<2147483647);}
 unsafe{NBZ_ROUT=reply;if i<64 {NBZ_RIN=b.raw[i];}}
 {let mut it=out.iter_mut().enumerate();if i>0 {let _=it.nth(i-1);}if let Some((index,w))=it.next(){*w=b.value(index);}}
 let expected=if i==j {reply[k]}else{before};
 if negative{assert_ne!(NBZ_qwords(out[j])[k],expected);}else{assert_eq!(NBZ_qwords(out[j])[k],expected);}
 assert_eq!(out.as_ptr(),optr);assert_eq!(out.len(),64);assert_eq!(out.capacity(),wc);assert_eq!(b.raw.as_ptr(),bptr);assert_eq!(b.raw.capacity(),rc);assert_eq!(b.terms,oldterms);
 unsafe{assert_eq!(NBZ_RCALLS,if i<64{4}else{0});}
 kani::cover!(i==0);kani::cover!(i==63);kani::cover!(i==64);kani::cover!(i!=j);
}
'''
attrs='''#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,KMX_copy_from_slice)]
#[kani::stub(<[u8]>::clone_from_slice,KMX_clone_from_slice)]
#[kani::stub(<[u8]>::to_vec,KMX_to_vec)]
#[kani::stub(Vec::<u8>::extend_from_slice,KMX_extend_from_slice)]
#[kani::stub(alloc::alloc::realloc,KMX_realloc)]
#[kani::unwind(65)]
'''
rows=[]
for case,extra in [('raw_word',''),('horner','#[kani::stub(aspis_core::field::WideExact::mul,NBZ_field::wide)]\n'),('finish','#[kani::stub(aspis_core::field::M31::reduce_u64,NBZ_reducer)]\n')]:
 for neg in [False,True]:
  name='NBZ_'+case+('_negative' if neg else '')
  s+=attrs+extra+'fn '+name+'(){NBZ_'+case+'_case('+str(neg).lower()+');}\n'
  rows.append(dict(harness='verifier::candidate::NBZ_steps::'+name,negative=neg,case=case))
Path('/tmp/NBZ_steps.rs').write_text(s)
(E/'NBZ_steps.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NBZ_steps.rs')))
(E/'NBZ_STEP_PLAN.json').write_text(json.dumps(rows,indent=2)+'\n')
