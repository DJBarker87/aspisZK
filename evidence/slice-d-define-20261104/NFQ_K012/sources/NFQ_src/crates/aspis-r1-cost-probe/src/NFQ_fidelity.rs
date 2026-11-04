// Rule (t) fidelity controls. State is exclusively local.
#[kani::ensures(|r| *r <= 2)]
#[kani::modifies()]
fn weak_usize()->usize{1}
#[kani::proof]
fn usize_real(){assert_eq!(weak_usize(),1);}
#[kani::proof] #[kani::stub_verified(weak_usize)]
fn usize_unimplied(){assert_eq!(weak_usize(),1);}
#[kani::modifies(&mut x[0])]
#[kani::ensures(|r| *r==1)]
fn usize_badframe(x:&mut [u8;2])->usize{x[1]=x[1].wrapping_add(1);1}
#[kani::proof_for_contract(usize_badframe)]
fn usize_frame(){let mut x:[u8;2]=kani::any();let _=usize_badframe(&mut x);}
#[kani::ensures(|r| r.is_some())]
#[kani::modifies()]
fn weak_option()->Option<(u8,usize)>{Some((7,37))}
#[kani::proof]
fn option_real(){assert_eq!(weak_option(),Some((7,37)));}
#[kani::proof] #[kani::stub_verified(weak_option)]
fn option_unimplied(){assert_eq!(weak_option(),Some((7,37)));}
#[kani::modifies(&mut x[0])]
#[kani::ensures(|r| r.is_some())]
fn option_badframe(x:&mut [u8;2])->Option<(u8,usize)>{x[1]=x[1].wrapping_add(1);Some((7,37))}
#[kani::proof_for_contract(option_badframe)]
fn option_frame(){let mut x:[u8;2]=kani::any();let _=option_badframe(&mut x);}
