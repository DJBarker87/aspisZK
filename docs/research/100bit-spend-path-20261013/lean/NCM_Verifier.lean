import NCM_LevelsDomain
import NCE_VerifierAdmission
import MultiproofConePhysicalVerify

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_Verifier
open Aeneas Aeneas.Std Result MultiproofConeRef NCE_OpeningCuts NCE_CarrierEffects
open MultiproofConeNodeDomain MultiproofConeNodeIteration MultiproofConeLevelIteration
open MultiproofConePhysicalTransport MultiproofConePhysicalViews
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
attribute [local instance] Classical.propDecidable

def returned (finish : NCE_VerifierCuts.Finish) (root : NCE_VerifierCuts.Digest)
    (physical : Slice U8) (out : Result reference.Level × Carrier) : Bool × Carrier :=
  match out.1 with
  | .ok (.Done _) => finish out.2 root physical
  | _ => (false,out.2)

def verify (node : Node) (entry : NCE_VerifierCuts.Entry) (exit : NCE_VerifierCuts.Exit)
    (finish : NCE_VerifierCuts.Finish) (pair range : NCE_AdmissionCuts.Predicate)
    (root : NCE_VerifierCuts.Digest) (physical : Slice U8) (s : Carrier) :
    Program Bytes State (Bool × Carrier) :=
  let admitted := NCE_VerifierAdmission.admitted entry pair range s physical.val.length
  if admitted.1 then bind (NCM_Levels.levels node exit 18 admitted.2 physical)
    (fun out => .done (returned finish root physical out))
  else .done (false,admitted.2)

/-- Observer for the EXISTING physical verifier, retaining its scratch and
caller log rather than choosing an independent execution. -/
def model (root : NCE_VerifierCuts.Digest) (physical : Slice U8) (s : Carrier) :
    Program Bytes State (Bool × Carrier) :=
  if OraclePortFrozenOrder.wellFormed ((live s.scratch 0 s.scratch.n.val).map Prod.fst) ∧ physical.val.length%32=0 then
    bind (annotate NCM_RowsObservation.levelScratch s
      (transport (MultiproofConePhysicalLevels.levels 18 s.scratch physical)))
      fun out => .done (MultiproofConePhysicalVerify.finish root physical out.1,out.2)
  else .done (false,s)

/-- Exact verifier result and chronological observation. The entry guard
establishes the node domain; every final guard bound comes from THAT height
execution. Rejection is not assumed away. Native premises are local cuts. -/
theorem association {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (law : ∀ input, D.digest hash input = ok (rawOracle H input))
    (node : Node) (row : NCE_Native_Row H node)
    (entry : NCE_VerifierCuts.Entry) (exit : NCE_VerifierCuts.Exit) (finish : NCE_VerifierCuts.Finish)
    (control : NCE_VerifierCuts.NCE_Native_Verifier entry exit finish)
    (pair range : NCE_AdmissionCuts.Predicate) (predicates : NCE_AdmissionCuts.NCE_Native_Admission pair range)
    (root : NCE_VerifierCuts.Digest) (physical : Slice U8) (s : Carrier)
    (size : physical.val.length ≤ 5504) (zero : s.scratch.«at».val = 0) :
    eval H (verify node entry exit finish pair range root physical s) = eval H (model root physical s) := by
  have admitted := NCE_VerifierAdmission.entry_model entry exit finish control pair range predicates s physical.val.length size
  simp only [verify,admitted,model]
  by_cases guard : OraclePortFrozenOrder.wellFormed ((live s.scratch 0 s.scratch.n.val).map Prod.fst) ∧ physical.val.length%32=0
  · simp only [guard,and_self,decide_true,↓reduceIte,eval_bind]
    have length : ((live s.scratch 0 s.scratch.n.val).map Prod.fst).length = s.scratch.n.val := by
      simp only [List.length_map,MultiproofConeRootGuard.live_length]
    have domain : Domain physical s.scratch := by
      refine ⟨?_,?_,by omega⟩
      · by_contra bad
        have empty : (live s.scratch 0 s.scratch.n.val).map Prod.fst = [] := by
          apply List.length_eq_zero_iff.mp
          omega
        exact guard.1.1 empty
      · have bounded := guard.1.2.1
        omega
    rw [NCM_Levels.observation D hash H law node row entry exit finish control 18 s physical size domain]
    simp only [annotate_eval]
    have totalHash : HashTotal D hash := fun input => ⟨rawOracle H input,law input⟩
    obtain ⟨out,doneResult⟩ := NCM_LevelsTotal.total D hash totalHash physical 18 s.scratch domain
    have value : (eval H (transport (MultiproofConePhysicalLevels.levels 18 s.scratch physical))).2 = ok out := by
      rw [transport_observation]
      exact (MultiproofConePhysicalLevels.levels_result D hash (rawOracle H) law _ _ _ domain).trans doneResult
    simp only [value,returned]
    cases out with
    | Stop stopped => rfl
    | Done after =>
      have nextDomain := NCM_LevelsDomain.preserved D hash totalHash physical 18 s.scratch after domain doneResult
      simp only [NCM_RowsObservation.levelScratch,MultiproofConePhysicalVerify.finish]
      rw [control.2.2 _ root physical nextDomain.2.1 nextDomain.2.2 size]
      rfl
  · simp only [guard,decide_false,Bool.false_eq_true,↓reduceIte]

#print axioms association
end AspisR1.NCM_Verifier
end
