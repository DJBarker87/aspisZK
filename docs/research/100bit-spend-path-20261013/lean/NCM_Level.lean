import NCM_RowsObservation

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_Level
open Aeneas Aeneas.Std Result MultiproofConeRef NCE_OpeningCuts NCE_CarrierEffects
open MultiproofConeNodeDomain MultiproofConeNodeIteration MultiproofConeLevelIteration
open MultiproofConePhysicalTransport
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def level (native : Node) (exit : NCE_VerifierCuts.Exit) (s : Carrier) (physical : Slice U8) : NCM_Rows.Run :=
  NCM_Rows.rows native exit s.scratch.n.val s physical 0#usize 0#usize

/-- The real row-count bound supplies sufficient fuel at the level entry. -/
theorem observation {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (law : ∀ input, D.digest hash input = ok (rawOracle H input))
    (native : Node) (cut : NCE_Native_Row H native)
    (entry : NCE_VerifierCuts.Entry) (exit : NCE_VerifierCuts.Exit) (finish : NCE_VerifierCuts.Finish)
    (control : NCE_VerifierCuts.NCE_Native_Verifier entry exit finish)
    (s : Carrier) (physical : Slice U8) (size : physical.val.length ≤ 5504)
    (domain : Domain physical s.scratch) :
    eval H (level native exit s physical) =
      eval H (annotate NCM_RowsObservation.levelScratch s
        (transport (MultiproofConePhysicalLevels.level s.scratch physical))) := by
  have row : RowDomain physical s.scratch 0#usize 0#usize :=
    ⟨domain.1,domain.2.1,by simp,by simp,domain.2.2⟩
  exact (NCM_Rows.association D hash H law native cut entry exit finish control _ s physical _ _ size row).trans
    (NCM_RowsObservation.observation D hash H law _ s physical _ _ size row (by simp))

/-- A level can reject, but cannot panic/diverge in the proved row domain. -/
theorem total {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (hashTotal : HashTotal D hash) (s : reference.Scratch) (physical : Slice U8)
    (domain : Domain physical s) :
    ∃ out, reference.level_rows D hash s physical 0#usize 0#usize = ok out := by
  have row : RowDomain physical s 0#usize 0#usize :=
    ⟨domain.1,domain.2.1,by simp,by simp,domain.2.2⟩
  rw [rows_eq_extracted D hash hashTotal physical s.n.val s _ _ row (by simp)]
  exact NCM_RowsTotal.total D hash hashTotal physical _ s _ _ row (by simp)

#print axioms observation
#print axioms total
end AspisR1.NCM_Level
end
