import R17CurrentDomainSource

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace R17CurrentDomainCanonical
open AspisR1QueryGeometryActual
abbrev ArithmeticCM := AspisR1Qm31ArithmeticProbe.field.CM31

def CanonicalM (x : U32) : Prop := x.val < 2147483647
def CanonicalCM (x : field.CM31) : Prop := CanonicalM x.a ∧ CanonicalM x.b

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem mul_success_canonical (a b z : U32)
    (h : AspisR1Qm31ArithmeticProbe.field.M31.mul a b = .ok z) : CanonicalM z := by
  obtain ⟨out,ho,_,hc⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod a b
  have he : out = z := Result.ok.inj (ho.symm.trans h)
  subst z
  exact hc

theorem sub_success_canonical (a b z : U32) (ha : CanonicalM a) (hb : CanonicalM b)
    (h : AspisR1Qm31ArithmeticProbe.field.M31.sub a b = .ok z) : CanonicalM z := by
  obtain ⟨out,ho,_,hc⟩ := AspisR1.ExtractedCurrentM31AddSub.current_sub_mod a b ha hb
  have he : out = z := Result.ok.inj (ho.symm.trans h)
  subst z
  exact hc

theorem double_success_canonical (a z : U32) (ha : CanonicalM a)
    (h : AspisR1Qm31ArithmeticProbe.field.M31.double a = .ok z) : CanonicalM z := by
  obtain ⟨out,ho,_,hc⟩ := AspisR1.ExtractedCurrentM31AddSub.current_add_mod a a ha ha
  have he : out = z := Result.ok.inj (ho.symm.trans h)
  subst z
  exact hc

/-- Every successful current complex multiplication returns canonical limbs,
even when its input limbs are arbitrary raw U32s. -/
theorem arithmetic_cm_mul_success_canonical (a b z : ArithmeticCM)
    (h : AspisR1Qm31ArithmeticProbe.field.CM31.mul a b = .ok z) :
    CanonicalM z.a ∧ CanonicalM z.b := by
  rw [AspisR1.ExtractedCurrentCM31Mul.generated_mul_graph] at h
  rcases bind_ok_inv h with ⟨m0,h0,h1tail⟩
  rcases bind_ok_inv h1tail with ⟨m1,h1,h2tail⟩
  rcases bind_ok_inv h2tail with ⟨product,_,h3tail⟩
  rcases bind_ok_inv h3tail with ⟨m2,h2,h4tail⟩
  rcases bind_ok_inv h4tail with ⟨low,hl,h5tail⟩
  rcases bind_ok_inv h5tail with ⟨high0,hh0,h6tail⟩
  rcases bind_ok_inv h6tail with ⟨high,hh,hout⟩
  have he : (⟨low,high⟩ : ArithmeticCM) = z := Result.ok.inj hout
  subst z
  have hc0 := mul_success_canonical a.a b.a m0 h0
  have hc1 := mul_success_canonical a.b b.b m1 h1
  obtain ⟨out,ho,_,hc⟩ := AspisR1.ExtractedCurrentReducer.current_wrapper_mod product
  have he2 : out = m2 := Result.ok.inj (ho.symm.trans h2)
  subst out
  have hc2 : CanonicalM m2 := hc
  have hcl := sub_success_canonical m0 m1 low hc0 hc1 hl
  have hch0 := sub_success_canonical m2 m0 high0 hc2 hc0 hh0
  exact ⟨hcl,sub_success_canonical high0 m1 high hch0 hc1 hh⟩

theorem cm_operations_success_canonical (a b c : field.CM31)
    (h : R17CurrentCM31Semantics.operations.mul a b = .ok c) : CanonicalCM c := by
  change (do
    let z ← AspisR1Qm31ArithmeticProbe.field.CM31.mul
      (R17CurrentCM31Semantics.toArithmetic a) (R17CurrentCM31Semantics.toArithmetic b)
    .ok (R17CurrentCM31Semantics.fromArithmetic z)) = .ok c at h
  rcases bind_ok_inv h with ⟨z,hz,hout⟩
  have he : R17CurrentCM31Semantics.fromArithmetic z = c := Result.ok.inj hout
  subst c
  exact arithmetic_cm_mul_success_canonical _ _ z hz

theorem fibre_point_success_canonical (u : domain.FibreIndex)
    (point : domain.Point field.M31)
    (h : fast_domain.fibre_point R17CurrentCM31Semantics.operations u = .ok point) :
    CanonicalM point.x ∧ CanonicalM point.y := by
  unfold fast_domain.fibre_point at h
  rcases bind_ok_inv h with ⟨_,_,h1⟩
  rcases bind_ok_inv h1 with ⟨_,_,h2⟩
  rcases bind_ok_inv h2 with ⟨_,_,h3⟩
  rcases bind_ok_inv h3 with ⟨left,_,h4⟩
  rcases bind_ok_inv h4 with ⟨_,_,h5⟩
  rcases bind_ok_inv h5 with ⟨_,_,h6⟩
  rcases bind_ok_inv h6 with ⟨right,_,h7⟩
  rcases bind_ok_inv h7 with ⟨product,hm,hout⟩
  have he : ({x := product.a,y := product.b} : domain.Point field.M31) = point := Result.ok.inj hout
  subst point
  exact cm_operations_success_canonical left right product hm

theorem line_node_success_canonical (u : domain.FibreIndex) (out : field.M31)
    (h : R17FibrePointLineNodeActual.line_node
      R17CurrentCM31Semantics.operations R17CurrentM31Semantics.operations u = .ok out) :
    CanonicalM out := by
  unfold R17FibrePointLineNodeActual.line_node at h
  rcases bind_ok_inv h with ⟨point,_,h1⟩
  rcases bind_ok_inv h1 with ⟨square,hs,h2⟩
  rcases bind_ok_inv h2 with ⟨twice,ht,ho⟩
  have hcs := mul_success_canonical point.x point.x square hs
  have hct := double_success_canonical square twice hcs ht
  exact sub_success_canonical twice (1#u32) out hct (by change (1 : Nat) < 2147483647; decide) ho

#print axioms arithmetic_cm_mul_success_canonical
#print axioms cm_operations_success_canonical
#print axioms fibre_point_success_canonical
#print axioms line_node_success_canonical
end R17CurrentDomainCanonical
