import S7Kani3CanonicalBackend
import S7Kani2OwnedRowRefinement

/-! Lossless carrier adapters between the emitted owned accumulator's four
U32 lanes and the frozen arithmetic backend. These are value-carrier joins;
physical proof/checkpoint byte decoding is outside this module. -/
set_option autoImplicit false
namespace AspisR1.S7JoinBackendCarriers
open Aeneas Aeneas.Std Result
open S7Kani2AccumulatorLoop (K)
open S7Kani2OwnedRowRefinement (powerLimb)
open ExtractedCurrentQM31Exact
open S7Kani3CanonicalBackend (P)

def toQ (x : K) : CurrentQM := ⟨⟨x.c0.1,x.c0.2⟩,⟨x.c1.1,x.c1.2⟩⟩
def fromQ (x : CurrentQM) : K := ⟨(x.c0.a,x.c0.b),(x.c1.a,x.c1.b)⟩
def decodeK (x : K) : QM31Exact := decode (toQ x)
def Canonical (x : K) : Prop := ∀ j : Fin 4, (powerLimb x j).val<P

theorem from_to (x : K) : fromQ (toQ x)=x := by
  cases x with
  | mk a b => cases a; cases b; rfl

theorem to_from (x : CurrentQM) : toQ (fromQ x)=x := by
  cases x with
  | mk a b => cases a; cases b; rfl

theorem canonical_iff (x : K) : Canonical x ↔ CurrentCanonicalQM (toQ x) := by
  constructor
  · intro h
    exact ⟨⟨by simpa [toQ,powerLimb] using h 0,
      by simpa [toQ,powerLimb] using h 1⟩,
      ⟨by simpa [toQ,powerLimb] using h 2,
      by simpa [toQ,powerLimb] using h 3⟩⟩
  · rintro ⟨⟨ha,hb⟩,⟨hc,hd⟩⟩ j
    fin_cases j <;> simpa [toQ,powerLimb] using (by first | exact ha | exact hb | exact hc | exact hd)

def multiply (x y : K) : Result K := do
  let z ← AspisR1Qm31ArithmeticProbe.field.QM31.mul (toQ x) (toQ y)
  ok (fromQ z)

/-- No multiply-call success or decoded-result premise is retained. -/
theorem multiply_exact (x y : K) (hx : Canonical x) (hy : Canonical y) :
    ∃ z, multiply x y=ok z ∧ Canonical z ∧ decodeK z=decodeK x*decodeK y := by
  obtain ⟨z,hz,hcan,hdecode⟩ := current_qm_mul_exact (toQ x) (toQ y)
    ((canonical_iff x).mp hx) ((canonical_iff y).mp hy)
  refine ⟨fromQ z,by simp only [multiply,hz,bind_tc_ok],?_,?_⟩
  · apply (canonical_iff _).mpr
    simpa only [to_from] using hcan
  · simpa only [decodeK,to_from] using hdecode

/-- The source canonicalization also handles arbitrary owned four-word rhs. -/
def canonicalize (x : K) : Result K := do
  let z ← S7Kani3CanonicalBackend.canonicalQM (toQ x)
  ok (fromQ z)

theorem canonicalize_exact (x : K) : ∃ y,
    canonicalize x=ok y ∧ Canonical y ∧ decodeK y=decodeK x := by
  obtain ⟨y,hy,hcan,hdecode⟩ := S7Kani3CanonicalBackend.canonical_qm_total (toQ x)
  refine ⟨fromQ y,by simp only [canonicalize,hy,bind_tc_ok],?_,?_⟩
  · apply (canonical_iff _).mpr
    simpa only [to_from] using hcan
  · simpa only [decodeK,to_from] using hdecode

#print axioms from_to
#print axioms to_from
#print axioms canonical_iff
#print axioms multiply_exact
#print axioms canonicalize_exact
end AspisR1.S7JoinBackendCarriers
