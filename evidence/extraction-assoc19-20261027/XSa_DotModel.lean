import XSa_DotWord
open Aeneas Aeneas.Std Result
open XSa_DotCarriers
set_option autoImplicit false
namespace XSa_DotModel

theorem model (self : Dot) (a b : XRn_Join_Release.fast_pairing.canonical.Q)
 (raw : Array U64 4#usize) (words : raw.val.map UScalar.val=XRn_Join_raw a b) :
 _root_.fast_pairing.canonical.Dot.push self a b =
 ok (⟨AspisR1DotPushLocal.Proof.updatedSums self.sums raw⟩ : Dot) := by
 rcases self with ⟨sums⟩
 obtain ⟨s0,s1,s2,s3,hs⟩ := List.length_eq_four.mp sums.property
 obtain ⟨r0,r1,r2,r3,hr⟩ := List.length_eq_four.mp raw.property
 have hs' : sums=Array.make 4#usize [s0,s1,s2,s3] := Subtype.ext hs
 have hr' : raw=Array.make 4#usize [r0,r1,r2,r3] := Subtype.ext hr
 subst sums
 subst raw
 unfold _root_.fast_pairing.canonical.Dot.push
 rw [←words]
 change ok (⟨Array.make 4#usize
   [XRn_Join_u64 (s0.val+XRn_Join_partial r0.val),
    XRn_Join_u64 (s1.val+XRn_Join_partial r1.val),
    XRn_Join_u64 (s2.val+XRn_Join_partial r2.val),
    XRn_Join_u64 (s3.val+XRn_Join_partial r3.val)]⟩ : Dot) = _
 simp only [AspisR1DotPushLocal.Proof.updatedSums,Array.make,List.zipWith,
   XSa_DotWord.update]

#print axioms model
end XSa_DotModel
