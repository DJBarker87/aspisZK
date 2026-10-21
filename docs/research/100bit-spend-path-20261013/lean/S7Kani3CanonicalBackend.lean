import S7Kani2BackendArithmetic
import Mathlib.Data.ZMod.Basic
set_option autoImplicit false
namespace AspisR1.S7Kani3CanonicalBackend
open Aeneas Aeneas.Std Result
open ExtractedCurrentQM31Exact
open S7Kani2BackendArithmetic (Q Wide Canonical CanonicalWide)
abbrev P : Nat := 2147483647

/-- Literal checked remainder used in the frozen canonical_qm31 closure. -/
def canonicalWord (x : U32) : Result U32 := x % 2147483647#u32

def canonicalQM (x : Q) : Result Q := do
  let a ← canonicalWord x.c0.a
  let b ← canonicalWord x.c0.b
  let c ← canonicalWord x.c1.a
  let d ← canonicalWord x.c1.b
  ok ⟨⟨a,b⟩,⟨c,d⟩⟩

theorem canonical_word_total (x : U32) : ∃ y, canonicalWord x=ok y ∧
    y.val=x.val%P ∧ y.val<P := by
  obtain ⟨y,hy,hv⟩ := WP.spec_imp_exists (UScalar.rem_spec x (y:=2147483647#u32) (by decide))
  exact ⟨y,hy,hv,by rw [hv]; exact Nat.mod_lt _ (by decide)⟩

/-- Actual four-coordinate canonicalisation is total for arbitrary U32 words
and preserves the exact field element. No canonical input is assumed. -/
theorem canonical_qm_total (x : Q) : ∃ y, canonicalQM x=ok y ∧
    Canonical y ∧ decode y=decode x := by
  obtain ⟨a,ha,va,ca⟩ := canonical_word_total x.c0.a
  obtain ⟨b,hb,vb,cb⟩ := canonical_word_total x.c0.b
  obtain ⟨c,hc,vc,cc⟩ := canonical_word_total x.c1.a
  obtain ⟨d,hd,vd,cd⟩ := canonical_word_total x.c1.b
  refine ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,by simp only [canonicalQM,ha,hb,hc,hd,bind_tc_ok],⟨⟨ca,cb⟩,⟨cc,cd⟩⟩,?_⟩
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext <;> simp [decode,va,vb,M31Exact,P]
  · apply QuadraticAlgebra.ext <;> simp [decode,vc,vd,M31Exact,P]

/-- Frozen mixed multiply canonicalises its unconstrained rhs first. This
removes the former canonical-rhs premise from the local backend law. -/
def mulMixed (x : Wide) (rhs : Q) : Result Wide := do
  let y ← canonicalQM rhs
  S7Kani2BackendArithmetic.mulWideCanonical x y

theorem mixed_total_exact (x : Wide) (rhs : Q) (hx : CanonicalWide x) :
    ∃ z, mulMixed x rhs=ok z ∧ CanonicalWide z ∧
      decode z.c0=decode x.c0*decode rhs ∧
      decode z.c1=decode x.c1*decode rhs := by
  obtain ⟨y,hy,hcy,hdy⟩ := canonical_qm_total rhs
  obtain ⟨z,hz,hcz,hz0,hz1⟩ := S7Kani2BackendArithmetic.mulWideCanonical_exact x y hx hcy
  exact ⟨z,by simp only [mulMixed,hy,hz,bind_tc_ok],hcz,by simpa only [hdy] using hz0,by simpa only [hdy] using hz1⟩

#print axioms canonical_word_total
#print axioms canonical_qm_total
#print axioms mixed_total_exact
end AspisR1.S7Kani3CanonicalBackend
