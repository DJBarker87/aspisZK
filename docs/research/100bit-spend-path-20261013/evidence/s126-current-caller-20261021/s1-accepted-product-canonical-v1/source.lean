import RawExtractedSemanticCallOpsV23
import ExtractedMaskQM31Mul
set_option autoImplicit false
namespace AspisS1AcceptedProductCanonical
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.ExtractedMaskTowerAdd

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (out : B)
    (h : (m >>= k)=ok out) : ∃ value, m=ok value ∧ k value=ok out := by
  cases m with
  | ok value => exact ⟨value,rfl,h⟩
  | fail error => cases h
  | div => cases h

private theorem scalar_mul_canonical (x y out : field.M31)
    (h : field.M31.mul x y=ok out) : out.val<P := by
  obtain ⟨z,called,_,canonical⟩ := AspisR1.ExtractedMaskReducer.current_mul_mod x y
  have same : z=out := Result.ok.inj (called.symm.trans h)
  simpa only [same] using canonical

private theorem scalar_reduce_canonical (x : U64) (out : field.M31)
    (h : field.M31.reduce_u64 x=ok out) : out.val<P := by
  obtain ⟨z,called,_,canonical⟩ := AspisR1.ExtractedMaskReducer.current_wrapper_mod x
  have same : z=out := Result.ok.inj (called.symm.trans h)
  simpa only [same] using canonical

private theorem scalar_sub_canonical (x y out : field.M31)
    (hx : x.val<P) (hy : y.val<P) (h : field.M31.sub x y=ok out) : out.val<P := by
  obtain ⟨z,called,_,canonical⟩ := AspisR1.ExtractedMaskM31AddSub.current_sub_mod x y hx hy
  have same : z=out := Result.ok.inj (called.symm.trans h)
  simpa only [same] using canonical

/-- ACCEPTED-ONLY for the actual CM31 source graph. The checked cross product
may fail on raw inputs; when the enclosing operation returns, all three
reducers and the subsequent canonical subtractions belong to that same call. -/
theorem cm_mul_success_canonical (x y out : field.CM31)
    (h : field.CM31.mul x y=ok out) : CanonicalCM out := by
  rw [AspisR1.ExtractedMaskCM31Mul.generated_mul_graph] at h
  obtain ⟨m0,e0,h⟩ := bind_success _ _ _ h
  obtain ⟨m1,e1,h⟩ := bind_success _ _ _ h
  obtain ⟨cross,ec,h⟩ := bind_success _ _ _ h
  obtain ⟨m2,e2,h⟩ := bind_success _ _ _ h
  obtain ⟨low,el,h⟩ := bind_success _ _ _ h
  obtain ⟨high0,eh0,h⟩ := bind_success _ _ _ h
  obtain ⟨high,eh,h⟩ := bind_success _ _ _ h
  have c0 := scalar_mul_canonical x.a y.a m0 e0
  have c1 := scalar_mul_canonical x.b y.b m1 e1
  have c2 := scalar_reduce_canonical cross m2 e2
  have cl := scalar_sub_canonical m0 m1 low c0 c1 el
  have ch0 := scalar_sub_canonical m2 m0 high0 c2 c0 eh0
  have ch := scalar_sub_canonical high0 m1 high ch0 c1 eh
  have same : (⟨low,high⟩ : field.CM31)=out := Result.ok.inj h
  rw [←same]
  exact ⟨cl,ch⟩

private theorem cm_add_canonical (x y out : field.CM31)
    (hx : CanonicalCM x) (hy : CanonicalCM y) (h : field.CM31.add x y=ok out) :
    CanonicalCM out := by
  obtain ⟨z,called,canonical,_,_⟩ := current_cm_add_mod x y hx hy
  have same : z=out := Result.ok.inj (called.symm.trans h)
  simpa only [same] using canonical
private theorem cm_sub_canonical (x y out : field.CM31)
    (hx : CanonicalCM x) (hy : CanonicalCM y) (h : field.CM31.sub x y=ok out) :
    CanonicalCM out := by
  obtain ⟨z,called,canonical,_,_⟩ := current_cm_sub_mod x y hx hy
  have same : z=out := Result.ok.inj (called.symm.trans h)
  simpa only [same] using canonical

private theorem r_total (x : field.CM31) (hx : CanonicalCM x) :
    ∃ z, field.mul_by_r x=ok z ∧ CanonicalCM z := by
  obtain ⟨a2,ea2,_,ca2⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod x.a x.a hx.1 hx.1
  obtain ⟨a,ea,_,ca⟩ := AspisR1.ExtractedMaskM31AddSub.current_sub_mod a2 x.b ca2 hx.2
  obtain ⟨b2,eb2,_,cb2⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod x.b x.b hx.2 hx.2
  obtain ⟨b,eb,_,cb⟩ := AspisR1.ExtractedMaskM31AddSub.current_add_mod x.a b2 hx.1 cb2
  exact ⟨⟨a,b⟩,by simp only [field.mul_by_r,field.M31.double,ea2,ea,eb2,eb,bind_tc_ok],⟨ca,cb⟩⟩

/-- ACCEPTED-ONLY canonical output of the actual QM31 multiplication graph.
No input-canonicality, child-success, or reducer-range premise is assumed.
This does not assert raw-input totality or decoded multiplication exactness. -/
theorem qm_mul_success_canonical (x y out : field.QM31)
    (h : field.QM31.mul x y=ok out) : CanonicalQM out := by
  unfold field.QM31.mul at h
  obtain ⟨m0,e0,h⟩ := bind_success _ _ _ h
  obtain ⟨m1,e1,h⟩ := bind_success _ _ _ h
  obtain ⟨a,ea,h⟩ := bind_success _ _ _ h
  obtain ⟨b,eb,h⟩ := bind_success _ _ _ h
  obtain ⟨m2,e2,h⟩ := bind_success _ _ _ h
  obtain ⟨r,er,h⟩ := bind_success _ _ _ h
  obtain ⟨low,el,h⟩ := bind_success _ _ _ h
  obtain ⟨d,ed,h⟩ := bind_success _ _ _ h
  obtain ⟨high,eh,h⟩ := bind_success _ _ _ h
  have c0 := cm_mul_success_canonical x.c0 y.c0 m0 e0
  have c1 := cm_mul_success_canonical x.c1 y.c1 m1 e1
  have c2 := cm_mul_success_canonical a b m2 e2
  obtain ⟨rModel,rCalled,rCanonical⟩ := r_total m1 c1
  have rEq : rModel=r := Result.ok.inj (rCalled.symm.trans er)
  have cr : CanonicalCM r := rEq ▸ rCanonical
  have cl := cm_add_canonical m0 r low c0 cr el
  have cd := cm_sub_canonical m2 m0 d c2 c0 ed
  have ch := cm_sub_canonical d m1 high cd c1 eh
  have same : (⟨low,high⟩ : field.QM31)=out := Result.ok.inj h
  rw [←same]
  exact ⟨cl,ch⟩

/-- Unconditional nominal transport of that same normally returned generated
source value. The existing generated/probe Result equality includes fail/div. -/
theorem generated_mul_success_canonical
    (x y out : AspisR1SemanticCallExtraction.aspis_core.field.QM31)
    (h : AspisR1SemanticCallExtraction.aspis_core.field.QM31.mul x y=ok out) :
    CanonicalQM (AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20.genQToProbe out) := by
  open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20 in
  have called : field.QM31.mul (genQToProbe x) (genQToProbe y)=ok (genQToProbe out) := by
    rw [←generated_qm_mul_eq_probe,h]
    rfl
  exact qm_mul_success_canonical _ _ _ called

#print axioms cm_mul_success_canonical
#print axioms qm_mul_success_canonical
#print axioms generated_mul_success_canonical
end AspisS1AcceptedProductCanonical
