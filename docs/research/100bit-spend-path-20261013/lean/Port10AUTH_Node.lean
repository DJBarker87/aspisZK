import Port10AUTH_Total
import Port9OR_P6Node
import Port10AUTH_Leaf

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_Node
open Aeneas Aeneas.Std Result MultiproofConeRef CheckpointBytes5Effect
open MultiproofConePhysicalProgram MultiproofConePhysicalTransport
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Proof-only total dictionary exposes the exact physical parent observation,
including checked mutation failure AFTER its emitted read. -/
theorem parent {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (s : reference.Scratch) (left right : CheckpointBytes5Effect.Digest)
    (ni cursor : Usize) (index : U32) (w : Usize) :
    Port9OR_Code.trace (Port10AUTH_Total.dictionary D H) hash (Port9OR_P6Node.parent s left right ni cursor index w)=
      eval (rawOracle H) (writer s left right ni cursor index w) := by
  simp only [Port9OR_P6Node.parent,Port9OR_Code.trace,Port10AUTH_Total.dictionary,
    Port10AUTH_Trace.trace_lift,writer,eval,rawOracle,List.append_nil]

/-- The concrete emitted node and raw canonical physical node have identical
complete observations under the proof-only total dictionary, on every input. -/
theorem node {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (s : reference.Scratch) (physical : Slice U8) (i w : Usize) :
    Port9OR_Code.trace (Port10AUTH_Total.dictionary D H) hash (Port9OR_P6Node.node s physical i w)=
      eval (rawOracle H) (MultiproofConePhysicalProgram.node s physical i w) := by
  simp only [Port9OR_P6Node.node,MultiproofConePhysicalProgram.node,Port9OR_Code.trace,
    MultiproofConeP6Callbacks.checked_eval,MultiproofConeP6Callbacks.conditional_eval,parent]
  repeat'
    first
    | rfl
    | (fail_if_no_progress dsimp only)
    | (fail_if_no_progress simp only [Port9OR_Code.trace,parent,eval])
    | (split <;> (try simp_all only [if_true,if_false]))
  all_goals rfl

/-- At actual accepted source nodes, primitive failure policy and all emitted
observations are preserved. No totality premise is required of the source. -/
theorem accepted {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (oracle : CheckpointBytes5Inputs.Oracle D hash H)
    (s : reference.Scratch) (physical : Slice U8) (i w : Usize) (out : reference.Row)
    (success : erase D hash (Port9OR_P6Node.node s physical i w)=ok out) :
    Port9OR_Code.trace D hash (Port9OR_P6Node.node s physical i w)=
      eval (rawOracle H) (MultiproofConePhysicalProgram.node s physical i w) :=
  (Port10AUTH_Total.accepted D hash H _ out oracle success).symm.trans (node D hash H s physical i w)

#print axioms parent
#print axioms node
#print axioms accepted
end AspisR1.Port10AUTH_Node
end
