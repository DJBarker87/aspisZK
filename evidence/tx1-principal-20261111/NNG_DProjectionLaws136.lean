import NNG_DProjection136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DProjection136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NNG_Array136

theorem q_ne {VL : RSL.VLib} {H : Type} (p : Representation VL H) (x y : Q) (hx : p.qDom x) (hy : p.qDom y) :
    decide (x ≠ y) = decide (p.q x ≠ p.q y) := by
  by_cases h : x = y
  · subst y; simp
  · have hn : p.q x ≠ p.q y := fun he => h (p.q_injective x y hx hy he)
    simp [h,hn]
#print axioms q_ne

theorem point_eq {VL : RSL.VLib} {H : Type} (p : Representation VL H)
    (x y : aspis_core.circle.SecureCirclePoint) :
    decide (x = y) = decide (p.point x = p.point y) := by
  by_cases h : x = y
  · subst y; simp
  · have hn : p.point x ≠ p.point y := fun he => h (p.point_injective he)
    simp [h,hn]
#print axioms point_eq

theorem b32_ext {x y : RSL.B32} (h : x.bytes = y.bytes) : x = y := by
  cases x
  cases y
  cases h
  rfl
#print axioms b32_ext

theorem root_some {VL : RSL.VLib} {H : Type} (p : Representation VL H)
    (s : Slice U8) (h : s.val.length = 32) :
    RSL.TX1_136.toB32 (p.bytes s) = some (p.b32 (NNG_Root32.value s h)) := by
  have len : (p.bytes s).length = 32 := (p.bytes_length s).trans h
  unfold RSL.TX1_136.toB32
  rw [dif_pos len]
  apply congrArg some
  apply b32_ext
  exact (p.root_bytes s h).symm
#print axioms root_some

theorem root_none {VL : RSL.VLib} {H : Type} (p : Representation VL H)
    (s : Slice U8) (h : s.val.length ≠ 32) :
    RSL.TX1_136.toB32 (p.bytes s) = none := by
  have len : (p.bytes s).length ≠ 32 := by rw [p.bytes_length]; exact h
  unfold RSL.TX1_136.toB32
  rw [dif_neg len]
#print axioms root_none

/-- Every successful output field is projected from the SAME actual source
locals; no final output or endpoint equality is a premise. -/
theorem verified_constructor {VL : RSL.VLib} {H W : Type} (p : Representation VL H)
    (s : Parent H W) (a : RSL.TX1_136.Args VL) (input : Inputs VL p a s) (alpha : Alpha) (claims : Claims) (extra before : K29)
    (state root : Array U8 32#usize) (z0 z1 : aspis_core.circle.SecureCirclePoint)
    (transcript : r1_wire.SemanticTranscript H) :
    verified p (⟨Array.make 2#usize [s.prefixValue.c1_root,root],s.challenges,alpha,claims,
      extra,before,state,Array.make 2#usize [z0,z1],transcript⟩ : r1_semantic.Verified H) =
    (⟨(VL.c1Root a.prefix_,p.b32 root),a.challenges,
      p.alpha alpha,p.claims claims,p.k29 extra,p.k29 before,p.b32 state,
      (p.point z0,p.point z1),p.transcript transcript⟩ : RSL.Verified VL) := by
  unfold verified
  rw [input.c1Root, ←input.challenges]
  rfl
#print axioms verified_constructor
end AspisR1.NNG_DProjection136
