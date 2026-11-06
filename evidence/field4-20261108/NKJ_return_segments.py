from pathlib import Path
p=Path(__file__).resolve().parent/'NKJ_segments.rs.txt';s=p.read_text();s+='''
// F: final converter's complete QM31 reply forwarded by the small helper.
#[kani::ensures(|out| if cfg!(NKJ_invert){*out!=reply}else{*out==reply})]
fn NKJ_return_segment(reply:QM31)->QM31 {reply}
#[kani::proof_for_contract(NKJ_return_segment)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NKJ_return_contract(){NKJ_return_segment(NKJ_any_q());}
#[kani::ensures(|out| if cfg!(NKJ_invert){out.c0.a.0!=out.c0.a.0}else{out.c0.a.0==out.c0.a.0})]
#[kani::modifies()]
fn NKJ_weak_q(s:QM31,frame:&mut u8)->QM31 {if cfg!(NKJ_modifies_bad){*frame=1;}s}
#[kani::proof_for_contract(NKJ_weak_q)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NKJ_q_weak_contract(){let mut f=0;NKJ_weak_q(NKJ_any_q(),&mut f);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NKJ_q_real_assert(){let q=NKJ_any_q();let mut f=0;let o=NKJ_weak_q(q,&mut f);assert!(o==q);}
#[kani::proof]
#[kani::stub_verified(NKJ_weak_q)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NKJ_q_unimplied(){let q=NKJ_any_q();let mut f=0;let o=NKJ_weak_q(q,&mut f);assert!(o==q);}
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn NKJ_q_copy(){let s=[NKJ_any_q()];let mut d=[QM31::ZERO];d.copy_from_slice(&s);assert!(if cfg!(NKJ_invert){d[0]!=s[0]}else{d[0]==s[0]});}
''';p.write_text(s);print('NKJ full QM31 reply/frame fidelity controls prepared')
