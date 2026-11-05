from pathlib import Path
import json
E=Path(__file__).resolve().parent
canon=' && '.join(f'a[{i}]<(1<<18)' for i in range(22))
inactive=' && '.join(f'(n>{i} || a[{i}]==0)' for i in range(22))
pred=' || '.join(f'(n>{i} && a[{i}]==x)' for i in range(22))
s='''use super::*;
fn NHB_contains_ref(a:&[u32;22],n:usize,x:u32)->bool {'''+pred+'''}
#[kani::requires(11<=n && n<22 && x<(1<<18) && '''+canon+' && '+inactive+''' && expected==NHB_contains_ref(&a,n,x))]
#[kani::ensures(|out| *out==expected)]
fn NHB_contains(a:[u32;22],n:usize,x:u32,expected:bool)->bool {
 let result=a[..n].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains)] #[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();let expected:bool=kani::any();
 NHB_contains(a,n,x,expected);
}
'''
(E/'NHB_ghost_contains.rs.txt').write_text(s)
(E/'NHB_GHOST_CONTAINS.json').write_text(json.dumps(dict(domain='11<=n<22; canonical accepted array, inactive zero, x18; expected is unique scalar input computed from prestate natural predicate',postcondition='one scalar Bool; no saved array capture',contains='actual native, not stubbed',source_restriction='no actual native contains result occurs in any requires',caller_lemmas=['NHB_Canonical.frame_preserves','NHB_Inactive.frame_preserves','NHB_Partition.complete','NHB_Observation.ghost_inputs']),indent=2)+'\n')
