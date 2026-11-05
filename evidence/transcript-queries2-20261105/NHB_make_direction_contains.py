from pathlib import Path
import json,sys
E=Path(__file__).resolve().parent;mode=sys.argv[1];n=11
canon=' && '.join(f'a[{i}]<(1<<18)' for i in range(22));inactive=' && '.join(f'(n>{i} || a[{i}]==0)' for i in range(22))
if mode=='absent':extra=' && '.join(f'a[{i}]!=x' for i in range(11));value='false'
elif mode=='first':extra='a[0]==x';value='true'
elif mode=='last':extra='a[10]==x';value='true'
else:raise ValueError(mode)
s='''use super::*;
#[kani::requires(n==11 && x<(1<<18) && '''+canon+' && '+inactive+' && '+extra+''')]
#[kani::ensures(|out| *out=='''+value+''')]
fn NHB_contains(a:[u32;22],n:usize,x:u32)->bool {
 let result=a[..11].contains(&x);
 #[cfg(not(NHB_invert))] {result}
 #[cfg(NHB_invert)] {!result}
}
#[kani::proof_for_contract(NHB_contains)] #[kani::unwind(24)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_contract() {
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains(a,n,x);
}
'''
(E/'NHB_direction_contains.rs.txt').write_text(s)
(E/'NHB_DIRECTION_CONTAINS.json').write_text(json.dumps(dict(length=n,direction=mode,status='partial branch-domain probe, not a full caller domain',value=value,precondition='source scalar absence or an explicit fixed-index witness; never the native contains result'),indent=2)+'\n')
