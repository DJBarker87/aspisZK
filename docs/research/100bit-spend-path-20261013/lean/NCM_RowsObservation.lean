import NCM_Rows
import NCM_TransportBind
import NCM_RowsTotal

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_RowsObservation
open Aeneas Aeneas.Std Result MultiproofConeRef NCE_OpeningCuts NCE_CarrierEffects
open MultiproofConeNodeDomain MultiproofConePhysicalTransport
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def levelScratch (before : reference.Scratch) : Result reference.Level → reference.Scratch
  | .ok (.Stop after) => after
  | .ok (.Done after) => after
  | _ => before

/-- Same-carrier row loop observes the existing physical program, including
its exact prefix on every failure. This is a symbolic induction, not height
or whole-buffer reduction. -/
theorem observation {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (law : ∀ input, D.digest hash input = ok (rawOracle H input))
    (fuel : Nat) (s : Carrier) (physical : Slice U8) (i w : Usize)
    (size : physical.val.length ≤ 5504) (domain : RowDomain physical s.scratch i w)
    (bound : s.scratch.n.val-i.val ≤ fuel) :
    eval H (NCM_Rows.rows NCM_RowProgress.model NCM_Rows.modelExit fuel s physical i w) =
      eval H (annotate levelScratch s (transport
        (MultiproofConePhysicalLevels.rows fuel s.scratch physical i w))) := by
  induction fuel generalizing s i w with
  | zero =>
    simp only [NCM_Rows.rows,NCM_Rows.terminal,MultiproofConePhysicalLevels.rows]
    split <;> simp only [transport,eval,annotate,levelScratch,NCM_Rows.modelExit]
  | succ fuel ih =>
    by_cases halt : i≥s.scratch.n
    · simp only [NCM_Rows.rows,MultiproofConePhysicalLevels.rows,halt,if_true,
        NCM_Rows.terminal,transport,annotate,eval,levelScratch,NCM_Rows.modelExit]
    · have active : i.val < s.scratch.n.val := by scalar_tac
      obtain ⟨out,log,observed,post⟩ := NCM_RowProgress.progress D hash H law
        NCM_RowProgress.model (fun _ _ _ _ _ _ _ => rfl) s physical i w size domain active
      have raw : eval H (transport (MultiproofConePhysicalProgram.node s.scratch physical i w)) = (log,ok out) := by
        have projected := congrArg (fun p => (p.1,p.2.1)) observed
        simpa only [NCM_RowProgress.model,annotate_eval] using projected
      rw [annotate_eval]
      simp only [NCM_Rows.rows,MultiproofConePhysicalLevels.rows,halt,if_false,
        MultiproofConePhysicalLevels.bindRun,NCM_TransportBind.transport_bind,
        eval_bind,raw,NCM_TransportBind.transport_checked,observed]
      cases out with
      | Stop stopped =>
        simp only [transport,eval,rowScratch,levelScratch,List.append_nil]
      | Next after ni nw =>
        simp only [rowScratch]
        have enough : after.n.val-ni.val ≤ fuel := by rw [post.1]; have := post.2.2.1; omega
        rw [ih {s with scratch:=after,log:=s.log++log} ni nw post.2.1 enough]
        simp only [annotate_eval,List.append_assoc]
        obtain ⟨result,returned⟩ := NCM_RowsTotal.total D hash
          (fun input => ⟨rawOracle H input,law input⟩) physical fuel after ni nw post.2.1 enough
        have value : (eval H (transport (MultiproofConePhysicalLevels.rows fuel after physical ni nw))).2 = ok result := by
          rw [transport_observation]
          exact (MultiproofConePhysicalLevels.rows_result D hash (rawOracle H) law fuel after physical ni nw).trans returned
        rw [value]
        cases result <;> rfl

#print axioms observation
end AspisR1.NCM_RowsObservation
end
