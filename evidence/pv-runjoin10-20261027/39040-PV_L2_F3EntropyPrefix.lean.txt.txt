import R1Z.PV_L2_F3Adaptive
import R1Z.SideChannelEntropyLaw

/-! Triangular coupling which fixes the entire E1 raw-seed tape and actual
public-nonce entropy state, while permuting the independent finite ROM-word
coordinate. This is an ideal finite-coordinate law. E1 is retained as the
source environmental boundary; native full L1 owner composition is open. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3EntropyPrefix
open R0Z R1Z.PV_L2_F3Words R1Z.PV_L2_F3Adaptive R1Z.ProverCommitPublicNonce40
  R1Z.ProverCommitLedger36 R1Z.CouplingR1PBin
attribute [local instance] Classical.propDecidable
abbrev Seeds := Fin 16 → Raw

def extend (seeds : Seeds) (i : Nat) : Raw := if hi : i < 16 then seeds ⟨i,hi⟩ else 0

def coupling (e : Seeds → Relabel) (n index : Nat) :
    (Seeds × (Fin n → Candidate)) ≃ (Seeds × (Fin n → Candidate)) where
  toFun p := (p.1,streamEquiv (e p.1) n index p.2)
  invFun p := (p.1,(streamEquiv (e p.1) n index).symm p.2)
  left_inv p := by simp only [Equiv.symm_apply_apply]
  right_inv p := by simp only [Equiv.apply_symm_apply]

/-- Keeps the returned seeds, every OS status, count, cursor and retained
ledger state simultaneously; it never relabels the successful seed pair. -/
theorem actual_entropy_preserved (e : Seeds → Relabel) (n index : Nat)
    (nonce : Path) (schedule : Schedule) (s : State)
    (p : Seeds × (Fin n → Candidate)) :
    generate nonce schedule (extend (coupling e n index p).1) s =
      generate nonce schedule (extend p.1) s := rfl

theorem candidate_history_preserved (e : Seeds → Relabel) (n index : Nat)
    (p : Seeds × (Fin n → Candidate)) :
    (fun i => decide (accepts ((coupling e n index p).2 i))) =
      (fun i => decide (accepts (p.2 i))) :=
  acceptance_history (e p.1) n index p.2

/-- Exact JOINT uniform-coordinate transport, conditional on the entire
seed-return tape. This does not identify the honest masked view with an
arbitrary test of unchanged raw words. -/
theorem entropy_words_joint (e : Seeds → Relabel) (n index : Nat)
    (nonce : Path) (schedule : Schedule) (s : State)
    (test : (Except EntropyError Private × State) → (Fin n → Candidate) → ℚ) :
    mean (fun p : Seeds × (Fin n → Candidate) =>
      test (generate nonce schedule (extend p.1) s) (coupling e n index p).2) =
    mean (fun p : Seeds × (Fin n → Candidate) =>
      test (generate nonce schedule (extend p.1) s) p.2) :=
  mp_equiv (coupling e n index) (fun p => test (generate nonce schedule (extend p.1) s) p.2)

#print axioms coupling
#print axioms actual_entropy_preserved
#print axioms candidate_history_preserved
#print axioms entropy_words_joint
end R1Z.PV_L2_F3EntropyPrefix
