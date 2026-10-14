import R1UnifiedSteps

/-! Symbolic state phases around the fixed reseed boundary in the unified run.
The semantic phase preserves the pre-reseed state at row 27 explicitly. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedPhases

open FS FS2 FS2.Duplex
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}
variable (p : Params M Cv L) (hD : 5 ≤ p.D) (H : Addr L → State)
  (pub : UnifiedSampler.Public L) (c1 : State) (payload : Nat → M)

def semanticState (j : Nat) : State :=
  if j = 27 then
    H (advanceA p (UnifiedRecords.absorbed p hD H pub c1 payload 26))
  else UnifiedRecords.previous p hD H pub c1 payload j

def openingState (j : Nat) : State :=
  UnifiedRun.state p hD H pub c1 payload (27 + j)

theorem semantic_before (j : Nat) (hj : j < 27) :
    semanticState p hD H pub c1 payload j =
      UnifiedRecords.previous p hD H pub c1 payload j := by
  simp [semanticState, Nat.ne_of_lt hj]

theorem semantic_end :
    semanticState p hD H pub c1 payload 27 =
      H (advanceA p (UnifiedRecords.absorbed p hD H pub c1 payload 26)) := by
  simp [semanticState]

theorem previous_state (i : Nat) (hi : i ≠ 0) :
    UnifiedRecords.previous p hD H pub c1 payload i =
      UnifiedRun.state p hD H pub c1 payload i := by
  cases i with
  | zero => contradiction
  | succ i => rfl

theorem semantic_root :
    semanticState p hD H pub c1 payload 0 =
      H (PublicInitFrame.addr pub.pubBytes pub.initFits c1) := by
  rw [semantic_before p hD H pub c1 payload 0 (by omega)]
  rfl

theorem semantic_step (hl : p.lbl 0 = 160)
    (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (j : Nat) (hj : j < 27) :
    semanticState p hD H pub c1 payload (j + 1) =
      H (advanceA p (UnifiedRecords.absorbed p hD H pub c1 payload j)) := by
  by_cases hlast : j = 26
  · subst j
    rw [semantic_end]
  · rw [semantic_before p hD H pub c1 payload (j + 1) (by omega),
      previous_state p hD H pub c1 payload (j + 1) (by omega)]
    exact UnifiedSteps.state_step p hD H pub c1 payload hl he j
      (by omega) (by omega)

theorem opening_root :
    openingState p hD H pub c1 payload 0 =
      H (UnifiedSteps.reseedAddress p hD H pub c1 payload) := by
  change UnifiedRun.state p hD H pub c1 payload 27 = _
  exact UnifiedSteps.reseed_step p hD H pub c1 payload

theorem opening_previous (j : Nat) :
    openingState p hD H pub c1 payload j =
      UnifiedRecords.previous p hD H pub c1 payload (27 + j) := by
  exact (previous_state p hD H pub c1 payload (27 + j) (by omega)).symm

theorem opening_step (hl : p.lbl 0 = 160)
    (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (j : Nat) (hj : j < 4) :
    openingState p hD H pub c1 payload (j + 1) =
      H (advanceA p (UnifiedRecords.absorbed p hD H pub c1 payload (27 + j))) := by
  change UnifiedRun.state p hD H pub c1 payload (27 + (j + 1)) = _
  rw [show 27 + (j + 1) = (27 + j) + 1 by omega]
  exact UnifiedSteps.state_step p hD H pub c1 payload hl he (27 + j)
    (by omega) (by omega)

#print axioms semantic_before
#print axioms semantic_end
#print axioms previous_state
#print axioms semantic_root
#print axioms semantic_step
#print axioms opening_root
#print axioms opening_previous
#print axioms opening_step

end AspisR1.UnifiedPhases
end
