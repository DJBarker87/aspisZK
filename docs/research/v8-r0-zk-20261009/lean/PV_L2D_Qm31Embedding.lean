import AspisR1ProducerRelease47.Funs
set_option autoImplicit false
namespace PV_L2D_Qm31Embedding
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47

theorem remainder_total (x : U32) : ∃ r, x % field.P = ok r := by
  obtain ⟨r,hr,_⟩ := WP.spec_imp_exists
    (UScalar.rem_spec x (y := field.P) (by rw [field.P]; decide))
  exact ⟨r,hr⟩
#print axioms remainder_total

theorem word_total (x : U32) : ∃ r,
    field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call () x = ok r := by
  obtain ⟨r,hr⟩ := remainder_total x
  exact ⟨r,by simp only [field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,hr,bind_tc_ok]⟩
#print axioms word_total

theorem canonical_total (x : field.QM31) : ∃ y, field.wide_exact.canonical_qm31 x = ok y := by
  obtain ⟨a,ha⟩ := word_total x.c0.a
  obtain ⟨b,hb⟩ := word_total x.c0.b
  obtain ⟨c,hc⟩ := word_total x.c1.a
  obtain ⟨d,hd⟩ := word_total x.c1.b
  exact ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,by simp only [field.wide_exact.canonical_qm31,ha,hb,hc,hd,bind_tc_ok]⟩
#print axioms canonical_total

/-- Complete Result law over the SHA-frozen emission, not a successful-run
projection. No native lower-limb canonicality claim is made here. -/
theorem embed_total (x : field.QM31) :
    ∃ y, field.wide_exact.WideExact.from_qm31 x = ok ⟨y,field.QM31.ZERO⟩ := by
  obtain ⟨y,hy⟩ := canonical_total x
  exact ⟨y,by simp only [field.wide_exact.WideExact.from_qm31,hy,bind_tc_ok]⟩
#print axioms embed_total

/-- The CT/non-CT canonicalizer difference can affect c0 but cannot affect
this field-domain predicate. `canonicalize` is not assumed to be total. -/
def embedWith (canonicalize : field.QM31 → Result field.QM31) (x : field.QM31) :
    Result field.wide_exact.WideExact := do
  let y ← canonicalize x
  ok ⟨y,field.QM31.ZERO⟩

theorem from_qm31_exact (x : field.QM31) :
    field.wide_exact.WideExact.from_qm31 x = embedWith field.wide_exact.canonical_qm31 x := rfl
#print axioms from_qm31_exact

theorem upper_zero (canonicalize : field.QM31 → Result field.QM31)
    (x : field.QM31) (out : field.wide_exact.WideExact)
    (h : embedWith canonicalize x = ok out) : out.c1=field.QM31.ZERO := by
  cases hc : canonicalize x with
  | ok y => simp only [embedWith,hc,bind_tc_ok,Result.ok.injEq] at h;cases h;rfl
  | fail error => simp [embedWith,hc] at h
  | div => simp [embedWith,hc] at h
#print axioms upper_zero

def limbs (x : field.wide_exact.WideExact) : List Nat :=
  [x.c0.c0.a.val,x.c0.c0.b.val,x.c0.c1.a.val,x.c0.c1.b.val,
   x.c1.c0.a.val,x.c1.c0.b.val,x.c1.c1.a.val,x.c1.c1.b.val]

theorem upper_limb_tail (canonicalize : field.QM31 → Result field.QM31)
    (x : field.QM31) (out : field.wide_exact.WideExact)
    (h : embedWith canonicalize x = ok out) :
    (limbs out).drop 4 = List.replicate 4 0 := by
  have he := upper_zero canonicalize x out h
  simp only [limbs,List.drop_succ_cons,List.drop_zero,he,field.QM31.ZERO]
  rfl
#print axioms upper_limb_tail

theorem frozen_upper_limb_tail (x : field.QM31) (out : field.wide_exact.WideExact)
    (h : field.wide_exact.WideExact.from_qm31 x = ok out) :
    (limbs out).drop 4 = List.replicate 4 0 :=
  upper_limb_tail _ x out h
#print axioms frozen_upper_limb_tail
end PV_L2D_Qm31Embedding
