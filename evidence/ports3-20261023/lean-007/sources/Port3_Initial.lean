import Port3_CheckpointInstall
import Port3_Constants

/-! Current constructor's emitted control skeleton, with concrete heap content
semantics. The retained extraction is s4-accumulator-new-current-extraction-v1;
all arithmetic constants use the current Stage2 carrier. Allocation availability
is an execution parameter and is derived on success, never postulated. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_Initial
open Aeneas Aeneas.Std Result VTop_Stages
open Port2_Initial

def mapFilled {AllocError : Type}
    (r : core.result.Result (alloc.vec.Vec KRaw) AllocError) :
    Result (core.result.Result (alloc.vec.Vec KRaw) verifier.Error) :=
  match r with | .Ok v => ok (.Ok v) | .Err _ => ok (.Err .Allocation)

/-- Parameterized emitted body, retaining map_err, Try and residual control. -/
def emitted {AllocError : Type}
    (finalLen : transport.Variant → Result Usize) (zero : Result KRaw)
    (filled : Usize → KRaw → Result (core.result.Result (alloc.vec.Vec KRaw) AllocError))
    (zeroWide : Result ERaw) (one : Result KRaw) (v : transport.Variant) :
    Result (core.result.Result verifier.Accumulator verifier.Error) := do
  let i ← finalLen v
  let q ← zero
  let r ← filled i q
  let r1 ← mapFilled r
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | core.ops.control_flow.ControlFlow.Continue weights => do
    let rhs ← zeroWide
    let power ← one
    ok (.Ok ⟨weights,rhs,power,0#usize⟩)
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      verifier.Accumulator (core.convert.FromSame verifier.Error) residual

def constructor (reserved : Bool) : transport.Variant →
    Result (core.result.Result verifier.Accumulator verifier.Error) :=
  emitted CheckpointBytes4Ops.finalLen (ok zeroK)
    (CheckpointBytes3Allocation.filled reserved) (ok zeroE) (ok oneK)

/-- Exact whole Result at S2: no success-only equation is used here. -/
theorem constructor_shell (reserved : Bool) :
    constructor reserved .S2 = newS2 (CheckpointBytes3Allocation.filled reserved 64#usize zeroK) := by
  unfold constructor emitted CheckpointBytes4Ops.finalLen
  simp only [bind_tc_ok]
  cases CheckpointBytes3Allocation.filled reserved 64#usize zeroK with
  | fail e => rfl
  | div => rfl
  | ok r => cases r <;> rfl

def install (base : Ops) (reserved : Bool) : Ops :=
  {Port3_CheckpointInstall.install base reserved with op12 := constructor reserved}

theorem accepted_fields (base : Ops) (reserved : Bool) (a : verifier.Accumulator)
    (accepted : (install base reserved).op12 .S2 = ok (.Ok a)) :
    reserved = true ∧ a.weights.val = List.replicate 64 zeroK ∧
      a.rhs = zeroE ∧ a.power = oneK ∧ a.next = 0#usize := by
  change constructor reserved .S2 = ok (.Ok a) at accepted
  rw [constructor_shell] at accepted
  obtain ⟨weights,success,eq⟩ := (newS2_success _ a).mp accepted
  obtain ⟨reservedEq,contents⟩ := CheckpointBytes3Allocation.filled_success_content
    reserved 64#usize zeroK weights success
  subst a
  exact ⟨reservedEq,contents,rfl,rfl,rfl⟩

theorem allocation_rejects (base : Ops) :
    (install base false).op12 .S2 = ok (.Err AdapterRw.aspis_r1_cost_probe.verifier.Error.Allocation) := by
  change constructor false .S2 = _
  rw [constructor_shell,CheckpointBytes3Allocation.filled_rejection]
  rfl

/-- Same numerical decoder as checkpoint/query; no fresh representation is
introduced. The raw constant identities are proved, with no backend premise. -/
theorem accepted_initial (base : Ops) (reserved : Bool) (a : verifier.Accumulator)
    (accepted : (install base reserved).op12 .S2 = ok (.Ok a)) :
    CheckpointBytes5Output.accumulator a = QueryAccumulator.initial := by
  have kzero := Port3_Constants.decode_zero_k
  have kone := Port3_Constants.decode_one_k
  have ezero := Port3_Constants.decode_zero_e
  obtain ⟨_,weights,rhs,power,next⟩ := accepted_fields base reserved a accepted
  unfold CheckpointBytes5Output.accumulator QueryAccumulator.initial
  congr 1
  · funext j
    simp only [weights,List.getElem?_replicate,if_pos j.isLt,Option.getD_some,kzero]
  · rw [rhs,ezero]
  · rw [power,kone]
  · rw [next]; rfl

#print axioms constructor_shell
#print axioms accepted_fields
#print axioms allocation_rejects
#print axioms accepted_initial
end AspisR1.Port3_Initial
end
