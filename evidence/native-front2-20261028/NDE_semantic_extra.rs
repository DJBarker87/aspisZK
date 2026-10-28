pub(super) fn canonical(q:QM31)->bool{q.c0.a.0<0x7fff_ffff&&q.c0.b.0<0x7fff_ffff&&q.c1.a.0<0x7fff_ffff&&q.c1.b.0<0x7fff_ffff}
pub(super) fn native_initial(v:CompiledVariant,a:QM31,b:QM31,c:QM31)->(QM31,QM31,QM31,QM31){let r=reference::initial_ref(v==CompiledVariant::Withdrawal,to_ref(a),to_ref(b),to_ref(c));(to_native(r.0),to_native(r.1),to_native(r.2),to_native(r.3))}
pub(super) fn native_scalar(v:CompiledVariant,p:bool,i:QM31,o:QM31,t:QM31,w:QM31)->[QM31;2]{let r=reference::scalar_ref(v==CompiledVariant::Withdrawal,p,to_ref(i),to_ref(o),to_ref(t),to_ref(w));[to_native(r[0]),to_native(r[1])]}
fn anyq()->QM31{let a:[u32;4]=kani::any();to_native(reference::Q{c0:reference::C{a:a[0],b:a[1]},c1:reference::C{a:a[2],b:a[3]}})}
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
#[kani::proof_for_contract(super::initial_variant_selectors)]
fn NDE_initial(){let v=if kani::any(){CompiledVariant::Withdrawal}else{CompiledVariant::PrivateTransfer};let a=anyq();let b=anyq();let c=anyq();kani::assume(canonical(a)&&canonical(b)&&canonical(c));let _=super::initial_variant_selectors(v,a,b,c);}
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
#[kani::proof_for_contract(super::scalar_lanes)]
fn NDE_scalar(){let v=if kani::any(){CompiledVariant::Withdrawal}else{CompiledVariant::PrivateTransfer};let p:bool=kani::any();let i=anyq();let o=anyq();let t=anyq();let w=anyq();kani::assume(canonical(o)&&canonical(t)&&canonical(w));let _=super::scalar_lanes(v,p,i,o,t,w);}
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDE_kmx::KMX_copy_nonoverlapping)]
#[kani::proof_for_contract(super::copy_variant)]
fn NDE_variant(){let v=if kani::any(){CompiledVariant::Withdrawal}else{CompiledVariant::PrivateTransfer};let _=super::copy_variant(v);}
