import PV_EVHB_ReserveWorld
import PV_EVH_NativeOperators
set_option autoImplicit false
noncomputable section
namespace PV_EVHB_SaltsReserve
open Aeneas Aeneas.Std ProverRwFull PV_EVH_Runtime
open R1Z.PV_FXM_ReserveWorld
variable [ExternalTypes]

/-- The extracted continuation after the actual initial reserve. Allocation
Err still goes through map_err and ?, and only Ok reaches the salt loop. -/
def afterReserve [ExternalFuns]
    (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (tag : Std.U8)
    (count : Usize) (r : core.result.Result Unit alloc.collections.TryReserveError)
    (salts : alloc.vec.Vec (Array Std.U8 32#usize)) :
    Result (core.result.Result host_commitment.PrivateSalts verifier.Error) := do
  let r1 ← core.result.Result.map_err
    prover.derive_private_salts.closure.Insts.CoreOpsFunctionFnOnceTupleTryReserveErrorError r ()
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
  match cf with
  | .Continue _ =>
    let result ← prover.derive_private_salts_loop reserved context hash tag count (.Ok salts) 0#usize
    core.result.Result.map (BuiltinFnOnce (alloc.vec.Vec (Array Std.U8 32#usize))
      host_commitment.PrivateSalts) result host_commitment.PrivateSalts.new
  | .Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      host_commitment.PrivateSalts (core.convert.FromSame verifier.Error) residual

theorem source_prefix [ExternalFuns]
    (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (tag : Std.U8) :
    prover.derive_private_salts reserved context hash tag = do
      let count ← aspis_core.r0.FIBRE_COUNT
      let (r,salts) ← alloc.vec.Vec.try_reserve_exact Global
        (alloc.vec.Vec.new (Array Std.U8 32#usize)) count
      afterReserve reserved context hash tag count r salts := rfl

/-- V183 is substituted into the extracted prover body itself. The count is
public FIBRE_COUNT and the original empty vector is retained on allocation Err.
No loop/callback result, allocator success or successful world is supplied. -/
theorem selected_prefix {S F : Type}
    (runtime : R1Z.PV_RunJoin_AllocatorWorld63.Runtime S F)
    (ops : ExternalFuns) (w : World S F)
    (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (tag : Std.U8) :
    letI : ExternalFuns := R1Z.PV_RunJoin_AllocatorWorld63.selectedAt runtime ops w
    prover.derive_private_salts reserved context hash tag = do
      let count ← aspis_core.r0.FIBRE_COUNT
      let v := alloc.vec.Vec.new (Array Std.U8 32#usize)
      let e := R1Z.PV_RunJoin_AllocatorWorld63.execute runtime w v count
      afterReserve reserved context hash tag count
        (R1Z.PV_FXM_ReserveSelected.returned runtime.encode e.returned) v := by
  letI : ExternalFuns := R1Z.PV_RunJoin_AllocatorWorld63.selectedAt runtime ops w
  rw [source_prefix]
  simp only [R1Z.PV_RunJoin_AllocatorWorld63.complete,bind_tc_ok,Aeneas.Std.uncurry]

/-- The initial request's capacity and byte size do not inspect a salt value.
Layout width/alignment and native metadata validity are still named obligations. -/
theorem initial_size (shape : Shape) (n : Usize)
    (metadata : R1Z.PV_FXM_ReserveSelected.Metadata
      (alloc.vec.Vec.new (Array Std.U8 32#usize))) :
    let b := R1Z.PV_FXM_ReserveSelected.buffer
      (alloc.vec.Vec.new (Array Std.U8 32#usize)) metadata
    b.values.length + n.val = n.val ∧
    (b.values.length+n.val)*shape.width = n.val*shape.width := by
  change 0+n.val=n.val ∧ (0+n.val)*shape.width=n.val*shape.width
  simp only [Nat.zero_add,and_self]

/-- Installing the stateful allocator does not reopen op11/op12 selection. -/
theorem operator_selection {S F : Type}
    (runtime : R1Z.PV_RunJoin_AllocatorWorld63.Runtime S F)
    (ops : ExternalFuns) (w : World S F)
    (selected : PV_EVH_OperatorFrames.Selection ops) :
    PV_EVH_OperatorFrames.Selection
      (R1Z.PV_RunJoin_AllocatorWorld63.selectedAt runtime ops w) where
  map := selected.map
  mapErr := selected.mapErr

#print axioms source_prefix
#print axioms selected_prefix
#print axioms initial_size
#print axioms operator_selection
end PV_EVHB_SaltsReserve
