import R1Z.PV_L2_F3CountedFibres

/-! The counted decoder erases to the actual consuming decoder used by the
owned source model. Counts do not introduce a padded or independently
resampled mask distribution. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3CountedErasure
open R1Z.ProverCommitSequentialFibres R1Z.PV_L2_F3CountedFibres
attribute [local instance] Classical.propDecidable
attribute [local irreducible] R1Z.ProverCommitWordCarrier.sourceBase
variable {W A : Type} [Fintype W]

def strip : (L : Nat) → Values (A × Nat) L → Values A L
  | 0,_ => PUnit.unit
  | L+1,out => (out.1.1,strip L out.2)

theorem counted_erases (d : W → Option A) (n L r : Nat) (ws : Fin n → W) :
    (counted d n L r ws).map (strip L) = decodeWords d n L r ws := by
  induction n generalizing L r with
  | zero => cases L <;> rfl
  | succ n ih =>
    cases L with
    | zero => rfl
    | succ L =>
      cases r with
      | zero => rfl
      | succ r =>
        simp only [counted,decodeWords,step,tagged]
        cases hd : d (ws 0) with
        | none =>
          simp only [Option.map_none]
          exact ih (L+1) r (fun j => ws j.succ)
        | some value =>
          simp only [Option.map_some]
          rw [← ih L 16 (fun j => ws j.succ)]
          cases hc : counted d n L 16 (fun j => ws j.succ) <;> rfl

/-- The ACTUAL Word decoder has equal successful fibres even after all
scalar counts are fixed. No new decoder law is assumed here. -/
theorem actual_word_conditioned {K : Type} [Field K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K]
    (n L r : Nat) (out out' : Values (R1Z.ProverCommitWordCarrier.sourceBase (K := K) × Nat) L)
    (same : counts L out = counts L out') :
    (Finset.univ.filter (fun ws : Fin n → R1Z.CommitReadsR1.Word =>
      counted (R1Z.ProverCommitWordCarrier.accepted (K := K)) n L r ws = some out)).card =
    (Finset.univ.filter (fun ws : Fin n → R1Z.CommitReadsR1.Word =>
      counted (R1Z.ProverCommitWordCarrier.accepted (K := K)) n L r ws = some out')).card :=
  @conditional_equal_fibres R1Z.CommitReadsR1.Word
    (R1Z.ProverCommitWordCarrier.sourceBase (K := K)) inferInstance
    (R1Z.ProverCommitWordCarrier.accepted (K := K)) 2
    (fun a => by
      convert R1Z.ProverCommitWordCarrier.accepted_equal_fibres (K := K) a using 1
      apply congrArg Finset.card
      ext w
      simp only [Finset.mem_filter,Finset.mem_univ,true_and])
    n L r out out' same

#print axioms counted_erases
#print axioms actual_word_conditioned
end R1Z.PV_L2_F3CountedErasure
