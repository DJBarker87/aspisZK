import CuSavingsWideCore
import ExtractedCurrentQM31Equality
set_option autoImplicit false
namespace AspisR1.CuSavingsWideArithmetic
open Aeneas Aeneas.Std Result AspisR1WideArithmetic

def embedding : ExactK →+* ExactE := QuadraticAlgebra.algebraMap

theorem rem_identity (x : U32) (hc : x.val<2147483647) :
    (x % field.P : Result U32)=.ok x := by
  have hP : field.P.val=2147483647 := by simp [field.P]
  obtain ⟨out,hr,hv⟩ := WP.spec_imp_exists
    (UScalar.rem_spec x (y:=field.P) (by rw [hP];decide))
  have he : out=x := UScalar.eq_of_val_eq (by rw [hv,hP,Nat.mod_eq_of_lt hc])
  simpa only [he] using hr

theorem canonical_identity (x : K) (hc : CanonicalK x) :
    field.wide_exact.canonical_qm31 x=.ok x := by
  rcases hc with ⟨⟨ha,hb⟩,⟨hc,hd⟩⟩
  simp only [field.wide_exact.canonical_qm31,
    field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
    rem_identity x.c0.a ha,rem_identity x.c0.b hb,
    rem_identity x.c1.a hc,rem_identity x.c1.b hd,bind_tc_ok]

theorem mixed (x : E) (q : K) (hx : CanonicalE x) (hq : CanonicalK q) :
    ∃ z, field.wide_exact.WideExact.mul_qm31 x q=.ok z ∧ CanonicalE z ∧
      decodeE z=decodeE x*embedding (decodeK q) := by
  obtain ⟨a,ha,hac,hav⟩ := k_mul x.c0 q hx.1 hq
  obtain ⟨b,hb,hbc,hbv⟩ := k_mul x.c1 q hx.2 hq
  refine ⟨⟨a,b⟩,?_,⟨hac,hbc⟩,?_⟩
  · simp only [field.wide_exact.WideExact.mul_qm31,canonical_identity q hq,ha,hb,bind_tc_ok]
  · apply QuadraticAlgebra.ext
    · simpa [decodeE,embedding] using hav
    · simpa [decodeE,embedding] using hbv

theorem k_injective (a b : K) (ha : CanonicalK a) (hb : CanonicalK b)
    (h : decodeK a=decodeK b) : a=b := by
  have he := (ExtractedCurrentQM31Equality.decode_eq_iff (toK a) (toK b) ha hb).mp h
  exact congrArg fromK he

theorem injective (a b : E) (ha : CanonicalE a) (hb : CanonicalE b)
    (h : decodeE a=decodeE b) : a=b := by
  have h0 := k_injective a.c0 b.c0 ha.1 hb.1 (congrArg QuadraticAlgebra.re h)
  have h1 := k_injective a.c1 b.c1 ha.2 hb.2 (congrArg QuadraticAlgebra.im h)
  cases a; cases b; simp_all

#print axioms embedding
#print axioms rem_identity
#print axioms canonical_identity
#print axioms mixed
#print axioms k_injective
#print axioms injective
end AspisR1.CuSavingsWideArithmetic
