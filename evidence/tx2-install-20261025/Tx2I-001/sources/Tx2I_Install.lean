import Op3I_Install
import VTop_Model
import Port4D_FinishInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.Tx2I_Install
open Aeneas Aeneas.Std Result

def variant : Op3I_Source.transport.Variant → VTop_Stages.transport.Variant
  | .S1 => .S1 | .S2 => .S2 | .D => .D

def error : Op3I_Source.verifier.Error → VTop_Stages.verifier.Error
  | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
  | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
  | .Checkpoint => .Checkpoint | .Allocation => .Allocation

/-- Same extracted parse_shape and pure std instance as Op3I; nominal carriers only. -/
def shape (proof : Slice U8) : Result (core.result.Result VTop_Stages.transport.Variant VTop_Stages.verifier.Error) := do
  let r ← Op3I_Source.verifier.candidate.parse_shape Op3I_Std.ops proof
  match r with
  | .Err e => ok (.Err (error e))
  | .Ok v => ok (.Ok (variant v))

def stage {W : Type} (base : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps W) : VTop_Stages.Ops :=
  {base with op3 := shape, op19 := Port4D_FinishInstall.finish finish}

/-- Only the authenticated TX2 adapter slot is fixed; TX1 stays in the Op3I chain. -/
def install {W : Type} (adapter : AdapterRw.Ops) (base : VTop_Stages.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W) : AdapterRw.Ops :=
  {adapter with op11 := VTop_Stages.verifier.candidate.tx2_authenticated (stage base finish)}

theorem shape_header (proof : Slice U8) (v : VTop_Stages.transport.Variant)
    (success : shape proof = ok (.Ok v)) :
    v = .S2 ∧ Op3I_Install.sourceBody proof = ok (.Ok .S2) ∧
    OraclePortHeader.accepts (MultiproofConeCanonical.bytesOf proof.val) = true := by
  unfold shape at success
  obtain ⟨r,call,rest⟩ := Op3I_ParseLaws.bind_success _ _ _ success
  cases r with
  | Err e => cases rest
  | Ok raw =>
    obtain ⟨rfl,_⟩ := Op3I_ParseLaws.source_success proof raw call
    cases rest
    have source : Op3I_Install.sourceBody proof = ok (.Ok .S2) := by
      simp only [Op3I_Install.sourceBody,call,bind_tc_ok,Op3I_Install.currentVariant]
    exact ⟨rfl,source,(Op3I_Install.header_of_success proof .S2 source).2⟩

theorem other_adapter_slots {W : Type} (adapter : AdapterRw.Ops) (base : VTop_Stages.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W) :
    {install adapter base finish with op11 := adapter.op11} = adapter := by cases adapter; rfl

theorem other_stage_slots {W : Type} (base : VTop_Stages.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps W) :
    {stage base finish with op3 := base.op3, op19 := base.op19} = base := by cases base; rfl

#print axioms shape_header
#print axioms other_adapter_slots
#print axioms other_stage_slots
end AspisR1.Tx2I_Install
end
