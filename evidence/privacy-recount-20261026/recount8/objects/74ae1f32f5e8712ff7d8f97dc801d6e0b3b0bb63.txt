import R1Z.ProverCommitOwnedModel
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitOwnedDecoder
open Aeneas Aeneas.Std Result AspisR1ProverStep8
open R0Z.FsStatement R1Z.FinalR1PBin
open R1Z.ProverCommitSequentialFibres R1Z.ProverCommitWordCarrier
open R1Z.ProverCommitFourSteps (collect)
variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
local notation "F" => sourceBase (K := K)

theorem valuesList_index {A : Type} (default : A) (L : Nat) (v : Values A L) (i : Fin L) :
    ((valuesList L v)[i.val]?).getD default = valuesEquiv A L v i := by
  induction L with
  | zero => exact Fin.elim0 i
  | succ L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [valuesList, Fin.val_succ, List.getElem?_cons_succ, valuesEquiv, Equiv.coe_fn_mk,
        Fin.cons_succ]
      exact ih v.2 j

theorem samples_model {blocks : Nat} (answers : Fin blocks → OracleAnswer)
    (domain : Slice U8) (capacity : blocks < 2^64) (L : Nat) (budget : 16*L ≤ blocks*8) :
    (samples (blockHash answers) domain L).map (List.map (fieldValue (K := K))) =
      (decodeWords (accepted (K := K)) (blocks*8) L 16 (wordsE blocks answers)).map (valuesList L) := by
  have erase_eq : erase (K := K) (collect (prover_commit_reference.limb_caller (blockHash answers) domain) L initial) =
      (samples (blockHash answers) domain L).map (List.map fieldValue) := by
    unfold samples erase
    cases h : collect (prover_commit_reference.limb_caller (blockHash answers) domain) L initial with
    | fail e => rfl
    | div => rfl
    | ok pair => rcases pair with ⟨sample, after⟩; cases sample <;> rfl
  rw [← erase_eq, ← sequence_collect]
  cases L with
  | zero => rw [decode_no_values]; rfl
  | succ L =>
    apply sequence_model answers domain capacity (blocks*8) L 16 initial
      (by simp [valid, initial]) (initial_cache answers) (by have zero : position initial = 0 := rfl; rw [zero]; omega) (by omega)
      (wordsE blocks answers)
    intro i
    apply congrArg (wordsE blocks answers)
    apply Fin.ext
    have zero : position initial = 0 := rfl
    simp only [zero, Nat.zero_add]

theorem mapped_lookup (values : List U32) (i : Nat) :
    ((values.map (fieldValue (K := K)))[i]?).getD (fieldValue 0#u32) =
      fieldValue (values[i]?.getD 0#u32) := by
  rw [List.getElem?_map]
  cases values[i]? <;> rfl

/-- Complete finite operational scalar collection equals the array decoder. -/
theorem samples_array {blocks : Nat} (answers : Fin blocks → OracleAnswer)
    (domain : Slice U8) (capacity : blocks < 2^64) (L : Nat) (budget : 16*L ≤ blocks*8) :
    (samples (blockHash answers) domain L).map
      (fun values => fun i : Fin L => fieldValue (K := K) (values[i.val]?.getD 0#u32)) =
      arrayDecode (accepted (K := K)) (blocks*8) L 16 (wordsE blocks answers) := by
  have h := congrArg (Option.map (fun values : List F =>
    fun i : Fin L => values[i.val]?.getD (fieldValue 0#u32)))
    (samples_model (K := K) answers domain capacity L budget)
  simp only [Option.map_map] at h
  have left : (fun values : List U32 => fun i : Fin L =>
      ((values.map (fieldValue (K := K)))[i.val]?).getD (fieldValue 0#u32)) =
      (fun values => fun i : Fin L => fieldValue (K := K) (values[i.val]?.getD 0#u32)) := by
    funext values i
    exact mapped_lookup values i.val
  have right : (fun v : Values F L => fun i : Fin L =>
      ((valuesList L v)[i.val]?).getD (fieldValue 0#u32)) = valuesEquiv F L := by
    funext v i
    exact valuesList_index (fieldValue 0#u32) L v i
  simpa only [Function.comp_def, left, right, arrayDecode] using h

#print axioms valuesList_index
#print axioms samples_model
#print axioms mapped_lookup
#print axioms samples_array
end R1Z.ProverCommitOwnedDecoder
