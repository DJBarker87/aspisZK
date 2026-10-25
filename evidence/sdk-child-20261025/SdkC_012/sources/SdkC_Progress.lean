import SdkC_NativeNode
import SdkC_Oracle
set_option autoImplicit false
noncomputable section
namespace AspisR1.SdkC_Progress
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeRef MultiproofConePhysicalProgram MultiproofConePhysicalTransport
open MultiproofConeNodeDomain MultiproofConeNodeIteration MultiproofConeLevelIteration

/-- The reified syntax is the same physical oracle program, before evaluation. -/
theorem program_reify {A : Type} (code : Run A) :
    SdkC_Oracle.program (SdkC_NativeNode.reify code) = transport code := by
  induction code with
  | done r => cases r <;> rfl
  | ask parts next ih =>
    simp only [SdkC_NativeNode.reify,SdkC_Oracle.program,transport]
    congr 1
    funext d
    exact ih (encodeState d)

def partialDigest (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) :
    aspis_core.digest.Digest32 Unit :=
  {coremarkerCopyInst := (SdkC_Source.dictionary hashv).coremarkerCopyInst,
    digest := (SdkC_Source.dictionary hashv).digest}

def idealDigest (H : Bytes → State) : aspis_core.digest.Digest32 Unit :=
  {coremarkerCopyInst := {cloneInst := {clone := fun q => ok q}},
    digest := fun _ parts => .ok (rawOracle H parts)}

/-- Only the actual returning node is transported. No unqueried input is
assumed to return and no independently successful node is selected. -/
theorem node_transport (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (s : reference.Scratch) (physical : Slice U8) (i w : Usize) (out : reference.Row)
    (source : reference.binary_step (partialDigest hashv) () s physical i w = .ok out) :
    reference.binary_step (idealDigest H) () s physical i w = .ok out := by
  have accepted := (SdkC_NativeNode.source_node hashv s physical i w []).trans source
  have exactRun := SdkC_Oracle.accepted_exact hashv sha256 H p1 syscall
    (SdkC_NativeNode.reify (node s physical i w)) out accepted
  have modeled : (eval H (transport (node s physical i w))).2 = .ok out := by
    rw [← program_reify,exactRun]
  rw [transport_observation] at modeled
  exact (node_result (idealDigest H) () (rawOracle H) (fun _ => rfl) s physical i w).symm.trans modeled

/-- Native progress is derived from the SAME successful partial-hash node.
This removes the total-hash precondition from the source-loop progress use. -/
theorem node_progress (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (physical : Slice U8) (s : reference.Scratch) (i w : Usize)
    (domain : RowDomain physical s i w) (active : i.val < s.n.val)
    (out : reference.Row)
    (source : reference.binary_step (partialDigest hashv) () s physical i w = .ok out) :
    Progress physical s i w out := by
  have transported := node_transport hashv sha256 H p1 syscall s physical i w out source
  obtain ⟨modeled,returned,progress⟩ := binary_step_progress (idealDigest H) ()
    (fun parts => ⟨rawOracle H parts,rfl⟩) physical s i w domain active
  have same : modeled = out := Result.ok.inj (returned.symm.trans transported)
  subst modeled
  exact progress

/-- All-input Result correspondence for the bounded native row loop under
the existing success-only syscall law. Errors and divergence stay explicit. -/
theorem rows_eq_source (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (sha256 H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (physical : Slice U8) (fuel : Nat) (s : reference.Scratch) (i w : Usize)
    (domain : RowDomain physical s i w) (bound : s.n.val-i.val ≤ fuel) :
    reference.level_rows (partialDigest hashv) () s physical i w =
      rows (fun s i w => reference.binary_step (partialDigest hashv) () s physical i w) fuel s i w := by
  induction fuel generalizing s i w with
  | zero =>
    have halt : i ≥ s.n := by change i.val ≥ s.n.val; omega
    rw [reference.level_rows]
    simp only [rows,if_pos halt]
  | succ fuel ih =>
    rw [reference.level_rows]
    simp only [rows]
    by_cases halt : i ≥ s.n
    · simp only [if_pos halt]
    · simp only [if_neg halt]
      cases call : reference.binary_step (partialDigest hashv) () s physical i w with
      | fail e => simp only [call,bind_tc_fail]
      | div => simp only [call,bind_tc_div]
      | ok out =>
        simp only [bind_tc_ok]
        have progress := node_progress hashv sha256 H p1 syscall physical s i w domain
          (by change ¬ i.val ≥ s.n.val at halt; omega) out call
        cases out with
        | Stop stopped => rfl
        | Next next ni nw =>
          exact ih next ni nw progress.2.1 (by rw [progress.1]; omega)

#print axioms program_reify
#print axioms node_transport
#print axioms node_progress
#print axioms rows_eq_source
end AspisR1.SdkC_Progress
end
