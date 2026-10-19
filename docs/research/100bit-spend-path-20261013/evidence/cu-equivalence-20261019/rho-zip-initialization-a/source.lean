import CuSavingsZipFill
import CuSavingsRhoInitRow
import CuSavingsRhoBatches

/-! Consume the exact extracted assignment in the original runtime zip/loan
iteration. This closes the assignment-loop behavior for equal-length inputs;
allocation and the full new-wrapper source binding remain explicit obligations.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoZipInitialization
open Aeneas Aeneas.Std Result AspisR1CuRho
open CuSavingsRhoInitRow CuSavingsRhoPushStep

def assignment (weight : field.QM31) : Result Raw4 :=
  AspisR1CuRhoInitRow.row (carrier weight)

def initialize (raw : Slice Raw4) (weights : Slice field.QM31) : Result (Slice Raw4) :=
  CuSavingsZipFill.fill assignment raw weights

theorem initialize_eq (raw : Slice Raw4) (weights : Slice field.QM31)
    (hlen : raw.val.length = weights.val.length) :
    initialize raw weights = .ok (initialState weights).raw := by
  exact CuSavingsZipFill.fill_success assignment initialRow raw weights
    (fun weight => row_success weight) hlen

def construct (raw : Slice Raw4) (weights : Slice field.QM31) : Result verifier.BatchedWeights := do
  let initialized ← initialize raw weights
  .ok {«raw»:=initialized,terms:=0#usize}

theorem construct_eq (raw : Slice Raw4) (weights : Slice field.QM31)
    (hlen : raw.val.length = weights.val.length) :
    construct raw weights = .ok (initialState weights) := by
  simp only [construct,initialize_eq raw weights hlen,bind_tc_ok]
  rfl

theorem pipeline_eq (raw : Slice Raw4) (weights : Slice field.QM31)
    (inputs : List (Result CuSavingsRhoBatches.Input))
    (hlen : raw.val.length = weights.val.length)
    (hc : ∀ weight ∈ weights.val,Canonical weight)
    (hcount : inputs.length ≤ 22)
    (hadmit : ∀ data,Result.ok data ∈ inputs →
      CuSavingsRhoBatches.Admitted data weights.val.length) :
    (do let state ← construct raw weights
        CuSavingsRhoBatches.optimized inputs state weights) =
      CuSavingsRhoBatches.reference inputs weights := by
  rw [construct_eq raw weights hlen]
  simp only [bind_tc_ok]
  exact CuSavingsRhoBatches.initialized_eq inputs weights hc hcount hadmit

#print axioms initialize_eq
#print axioms construct_eq
#print axioms pipeline_eq
end AspisR1.CuSavingsRhoZipInitialization
