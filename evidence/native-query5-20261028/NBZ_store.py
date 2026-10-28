from pathlib import Path
import difflib,json
E=Path(__file__).resolve().parent
s=Path('/tmp/NBZ_windows.rs').read_text().replace('//!','//');s=s[:s.index('fn NBZ_window<')]
s+='''
fn NBZ_get_k(q:&K,k:usize)->u32{match k{0=>q.c0.a.0,1=>q.c0.b.0,2=>q.c1.a.0,_=>q.c1.b.0}}
fn NBZ_set_k(q:&mut K,k:usize,value:u32){match k{0=>q.c0.a.0=value,1=>q.c0.b.0=value,2=>q.c1.a.0=value,_=>q.c1.b.0=value}}
fn NBZ_indices(rows:usize,cols:usize,class:u8)->(usize,usize,usize,usize){
 let i:usize=kani::any();let j:usize=kani::any();let k:usize=kani::any();let l:usize=kani::any();
 kani::assume(i<rows&&j<rows&&k<cols&&l<cols);
 match class{0=>kani::assume(i==j&&k==l),1=>kani::assume(i==j&&k!=l),_=>kani::assume(i!=j)}
 (i,j,k,l)
}
fn NBZ_raw_store_case(class:u8,negative:bool){
 let cap=NBZ_cap::<[u64;4]>(64);let mut raw=NBZ_raw(cap);let ptr=raw.as_ptr();let(i,j,k,l)=NBZ_indices(64,4,class);
 let old=raw[j][l];let reply:u64=kani::any();raw[i][k]=reply;
 let expected=if class==0{reply}else{old};
 if negative{assert_ne!(raw[j][l],expected);}else{assert_eq!(raw[j][l],expected);}
 assert_eq!(raw.as_ptr(),ptr);assert_eq!(raw.len(),64);assert_eq!(raw.capacity(),cap);kani::cover!(i==63&&k==3);kani::cover!(cap>64);
}
fn NBZ_weight_store_case(class:u8,negative:bool){
 let cap=NBZ_cap::<K>(64);let mut weights=NBZ_weights(cap);let ptr=weights.as_ptr();let(i,j,k,l)=NBZ_indices(64,4,class);
 let old=NBZ_get_k(&weights[j],l);let reply:u32=kani::any();NBZ_set_k(&mut weights[i],k,reply);
 let expected=if class==0{reply}else{old};
 if negative{assert_ne!(NBZ_get_k(&weights[j],l),expected);}else{assert_eq!(NBZ_get_k(&weights[j],l),expected);}
 assert_eq!(weights.as_ptr(),ptr);assert_eq!(weights.len(),64);assert_eq!(weights.capacity(),cap);kani::cover!(i==63&&k==3);kani::cover!(cap>64);
}
fn NBZ_inverse_store_case(class:u8,negative:bool){
 let cap=NBZ_cap::<[M31;5]>(10);let mut inv=NBZ_inverses(cap);let ptr=inv.as_ptr();let(i,j,k,l)=NBZ_indices(10,5,class);
 let old=inv[j][l].0;let reply:u32=kani::any();inv[i][k].0=reply;
 let expected=if class==0{reply}else{old};
 if negative{assert_ne!(inv[j][l].0,expected);}else{assert_eq!(inv[j][l].0,expected);}
 assert_eq!(inv.as_ptr(),ptr);assert_eq!(inv.len(),10);assert_eq!(inv.capacity(),cap);kani::cover!(i==9&&k==4);kani::cover!(cap>10);
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
for kind in ['raw','weight','inverse']:
 for cls in range(3):
  for neg in [False,True]:
   name=f'NBZ_{kind}_store_{cls}'+('_negative' if neg else '')
   s+=attrs+'fn '+name+'(){NBZ_'+kind+'_store_case('+str(cls)+','+str(neg).lower()+');}\n'
   rows.append(dict(harness='verifier::candidate::NBZ_store::'+name,case=kind+'_class'+str(cls),negative=neg))
Path('/tmp/NBZ_store.rs').write_text(s)
(E/'NBZ_store.patch').write_text(''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NBZ_store.rs')))
(E/'NBZ_STORE_PLAN.json').write_text(json.dumps(rows,indent=2)+'\n')
