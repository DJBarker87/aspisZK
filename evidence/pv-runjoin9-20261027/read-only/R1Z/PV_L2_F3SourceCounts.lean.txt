import R1Z.PV_L2_F3CountedArrays
import R1Z.ProverCommitOwnedModel

/-! Counted scalar collection using the ACTUAL extracted next operation.
Every hash refill, cached-word read and rejection uses the owned source state.
The model join is by symbolic stream induction, not an assumed trace join. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3SourceCounts
open Aeneas Aeneas.Std Result AspisR1ProverStep8
open R0Z.FsStatement R1Z.FinalR1PBin R1Z.ProverCommitOwnedDecoder
open R1Z.ProverCommitStepLoop (State Hash)
open R1Z.ProverCommitSequentialFibres R1Z.ProverCommitWordCarrier
open R1Z.PV_L2_F3CountedFibres
attribute [local instance] Classical.propDecidable
variable {K : Type} [Field K] [Algebra (ZMod AspisCircleGroupOrder.P) K]
local notation "F" => sourceBase (K := K)

def source (hash : Hash) (domain : Slice U8) : Nat → Nat → State → Option (List (F × Nat))
  | 0,_,_ => some []
  | L+1,0,_ => none
  | L+1,r+1,state =>
      match prover_commit_reference.next hash domain state with
      | .ok (word,after) =>
        if word &&& 2147483647#u32 < aspis_core.field.P then
          (source hash domain L 16 after).map ((fieldValue (word &&& 2147483647#u32),17-(r+1))::·)
        else source hash domain (L+1) r after
      | _ => none
termination_by L r _ => 16*L+r

theorem counted_no_values {W A : Type} [Fintype W] (d : W → Option A)
    (n r : Nat) (ws : Fin n → W) :
    (counted d n 0 r ws).map (valuesList 0) = some [] := by cases n <;> rfl

theorem counted_list_step {W A : Type} [Fintype W] (d : W → Option A)
    (n L r : Nat) (ws : Fin (n+1) → W) :
    (counted d (n+1) (L+1) (r+1) ws).map (valuesList (L+1)) =
      match d (ws 0) with
      | none => (counted d n (L+1) r (fun j => ws j.succ)).map (valuesList (L+1))
      | some a => ((counted d n L 16 (fun j => ws j.succ)).map (valuesList L)).map ((a,17-(r+1))::·) := by
  simp only [counted,step,tagged]
  cases hd : d (ws 0) with
  | none => rfl
  | some a => cases ht : counted d n L 16 (fun j => ws j.succ) <;> rfl

/-- Actual source calls and the counted finite-word decoder have exactly the
same successful values AND per-scalar counts on every supported cache state. -/
theorem source_model {blocks : Nat} (answers : Fin blocks → OracleAnswer)
    (domain : Slice U8) (capacity : blocks < 2^64) (n L r : Nat)
    (state : State) (before : valid blocks state) (cache : cacheValid answers state)
    (fits : position state+n ≤ blocks*8) (budget : r+16*L ≤ n)
    (ws : Fin n → R1Z.CommitReadsR1.Word)
    (agrees : ∀ i : Fin n,
      wordsE blocks answers ⟨position state+i.val, by have := i.isLt; omega⟩ = ws i) :
    source (K := K) (blockHash answers) domain (L+1) r state =
      (counted (accepted (K := K)) n (L+1) r ws).map (valuesList (L+1)) := by
  induction n generalizing L r state with
  | zero =>
    have zr : r=0 := by omega
    subst r
    simp only [source,counted,Option.map_none]
  | succ n ih =>
    cases r with
    | zero => simp only [source,counted,Option.map_none]
    | succ r =>
      obtain ⟨word,after,hn⟩ := next_total answers domain state before (by omega)
      have progress := next_progress answers domain state after word capacity before hn
      obtain ⟨nextcache,bound,wordeq⟩ := next_cache answers domain state after word capacity before cache hn
      have head : accepted (K := K) (ws 0) =
          if word &&& 2147483647#u32 < aspis_core.field.P then
            some (fieldValue (word &&& 2147483647#u32)) else none := by
        rw [←agrees 0]
        have eq : (⟨position state+(0 : Fin (n+1)).val,by have := (0 : Fin (n+1)).isLt;omega⟩ : Fin (blocks*8)) =
            ⟨position state,bound⟩ := by apply Fin.ext;simp
        rw [eq,←wordeq,accepted_word]
      have fit : position after+n≤blocks*8 := by omega
      have tail : ∀ i : Fin n,
          wordsE blocks answers ⟨position after+i.val,by have := i.isLt;omega⟩ = ws i.succ := by
        intro i
        rw [←agrees i.succ]
        apply congrArg (wordsE blocks answers)
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      rw [source,hn,counted_list_step,head]
      simp only []
      by_cases yes : word &&& 2147483647#u32 < aspis_core.field.P
      · simp only [if_pos yes]
        cases L with
        | zero => rw [counted_no_values];simp only [source]
        | succ L =>
          rw [ih L 16 after progress.1 nextcache fit (by omega) (fun i => ws i.succ) tail]
      · simp only [if_neg yes]
        exact ih L r after progress.1 nextcache fit (by omega) (fun i => ws i.succ) tail

#print axioms counted_no_values
#print axioms counted_list_step
#print axioms source_model
end R1Z.PV_L2_F3SourceCounts
