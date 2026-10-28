import NCM_LevelsTotal

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_Levels
open Aeneas Aeneas.Std Result MultiproofConeRef NCE_OpeningCuts NCE_CarrierEffects
open MultiproofConeNodeDomain MultiproofConeNodeIteration MultiproofConeLevelIteration
open MultiproofConePhysicalTransport
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def levels (native : Node) (exit : NCE_VerifierCuts.Exit) : Nat → Carrier → Slice U8 → NCM_Rows.Run
  | 0,s,_ => .done (ok (.Done s.scratch),s)
  | height+1,s,physical => bind (NCM_Level.level native exit s physical) fun returned =>
      match returned.1 with
      | .fail error => .done (.fail error,returned.2)
      | .div => .done (.div,returned.2)
      | .ok (.Stop stopped) => .done (ok (.Stop stopped),returned.2)
      | .ok (.Done _) => levels native exit height returned.2 physical

/-- Height induction on the SAME native row returns, preserving both the
ordered requests and the caller log on early rejection. Only the native
one-row and phase-selected verifier cuts are consumed. -/
theorem observation {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (law : ∀ input, D.digest hash input = ok (rawOracle H input))
    (native : Node) (cut : NCE_Native_Row H native)
    (entry : NCE_VerifierCuts.Entry) (exit : NCE_VerifierCuts.Exit) (finish : NCE_VerifierCuts.Finish)
    (control : NCE_VerifierCuts.NCE_Native_Verifier entry exit finish)
    (height : Nat) (s : Carrier) (physical : Slice U8) (size : physical.val.length ≤ 5504)
    (domain : Domain physical s.scratch) :
    eval H (levels native exit height s physical) =
      eval H (annotate NCM_RowsObservation.levelScratch s
        (transport (MultiproofConePhysicalLevels.levels height s.scratch physical))) := by
  have totalHash : HashTotal D hash := fun input => ⟨rawOracle H input,law input⟩
  induction height generalizing s with
  | zero => rfl
  | succ height ih =>
    obtain ⟨out,returned⟩ := NCM_Level.total D hash totalHash s.scratch physical domain
    have value : (eval H (transport (MultiproofConePhysicalLevels.level s.scratch physical))).2 = ok out := by
      rw [transport_observation]
      exact (MultiproofConePhysicalLevels.level_result D hash (rawOracle H) law _ _ domain).trans returned
    simp only [levels,eval_bind,NCM_Level.observation D hash H law native cut entry exit finish control s physical size domain,
      annotate_eval,value]
    simp only [MultiproofConePhysicalLevels.levels,MultiproofConePhysicalLevels.bindRun,
      NCM_TransportBind.transport_bind,eval_bind,NCM_TransportBind.transport_checked,value]
    cases out with
    | Stop stopped =>
      simp only [NCM_RowsObservation.levelScratch,transport,eval,List.append_nil]
    | Done after =>
      have nextDomain := level_preserve D hash totalHash physical s.scratch after domain returned
      simp only [NCM_RowsObservation.levelScratch]
      rw [ih {s with scratch:=after,log:=s.log++(eval H (transport (MultiproofConePhysicalLevels.level s.scratch physical))).1} nextDomain]
      simp only [annotate_eval,List.append_assoc]
      obtain ⟨result,doneResult⟩ := NCM_LevelsTotal.total D hash totalHash physical height after nextDomain
      have finalValue : (eval H (transport (MultiproofConePhysicalLevels.levels height after physical))).2 = ok result := by
        rw [transport_observation]
        exact (MultiproofConePhysicalLevels.levels_result D hash (rawOracle H) law height after physical nextDomain).trans doneResult
      rw [finalValue]
      cases result <;> rfl

#print axioms observation
end AspisR1.NCM_Levels
end
