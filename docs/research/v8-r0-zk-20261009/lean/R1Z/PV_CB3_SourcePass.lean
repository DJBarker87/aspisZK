import R1Z.PV_CB3_WordArithmetic
import R1Z.PV_CB3_SamplerDivision
namespace R1Z.PV_CB3_SourcePass
open Aeneas Aeneas.Std Result
open PV_CB3_SamplerWord (base radix)
set_option autoImplicit false

def values (words : List U32) : List Nat := words.map (fun w => w.val)

/-- Monadic composition of the exact extracted scalar step. It retains all
Result outcomes; no successful-output contract is assumed. -/
def pass : List U32 → Result (List U32 × U64)
  | [] => ok ([], 0#u64)
  | word :: words => do
    let (high, prior) ← pass words
    let (quotient, remainder) ← PV_CB3_ShippedOp249word.reference_split.word_step word prior
    ok (quotient :: high, remainder)

theorem total (words : List U32) :
    ∃ (quotient : List U32) (remainder : U64),
      pass words = ok (quotient,remainder) ∧
      values quotient = (PV_CB3_SamplerDivision.divideLE base radix (values words)).1 ∧
      remainder.val = (PV_CB3_SamplerDivision.divideLE base radix (values words)).2 := by
  induction words with
  | nil => exact ⟨[],0#u64,rfl,rfl,rfl⟩
  | cons w ws ih =>
    obtain ⟨high,prior,hp,hv,hr⟩ := ih
    have bound : prior.val < base := by
      rw [hr]
      exact PV_CB3_SamplerDivision.remainder_lt base radix (by unfold base; omega) _
    obtain ⟨q,r,hs,hqv,hrv⟩ := PV_CB3_WordArithmetic.total w prior bound
    refine ⟨q :: high,r,?_,?_,?_⟩
    · simp only [pass,hp,bind_tc_ok,hs]
    · change q.val :: values high =
        (PV_CB3_SamplerDivision.divideLE base radix (w.val :: values ws)).1
      simp only [PV_CB3_SamplerDivision.divideLE]
      rw [hqv,hv,hr]
      rfl
    · change r.val = (PV_CB3_SamplerDivision.divideLE base radix (w.val :: values ws)).2
      simp only [PV_CB3_SamplerDivision.divideLE]
      rw [hrv,hr]
      rfl

theorem canonical_result (words : List U32) :
    ∃ q r, pass words = ok (q,r) ∧ r.val < base := by
  obtain ⟨q,r,h,_,hr⟩ := total words
  refine ⟨q,r,h,?_⟩
  rw [hr]
  exact PV_CB3_SamplerDivision.remainder_lt base radix (by unfold base; omega) _

#print axioms total
#print axioms canonical_result
end R1Z.PV_CB3_SourcePass
