import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_348
open RSL PCM PCM.Computation
structure Args where
  plan : DispatchPlan
  proof : AccountInfo
  master : AccountInfo
  checkpoint : AccountInfo
  lane : AccountInfo
  registry : List AccountInfo
  verifier_program : AccountInfo
  verifier_checkpoint : Option AccountInfo
structure Children where
  requireProgram : Child (AccountInfo × B32) Unit
  proofTransport : Child (AccountInfo × AccountInfo × Option AccountInfo) B32
  distinctCheckpoint : Child (Option AccountInfo × AccountInfo × AccountInfo × AccountInfo × List AccountInfo) Unit
  decodeResult : Child Bytes TerminalResult

def readonly (a : AccountInfo) : PCM.Meta := ⟨a.key,false,false⟩
/-- Deployed invariant-lane-audit and split-checkpoint arms. Actual initial
Vec allocations, optional growth, Box::new, and possible boxed-slice shrink
are distinct sites. Runtime callbacks are named slots, never SHA models. -/
def Ref (C : Children) (runtime : Runtime) (a : Args) : Computation AuthenticatedResult := do
  C.requireProgram.call (a.verifier_program,a.plan.selected_verifier)
  let _ ← C.proofTransport.call (a.verifier_program,a.proof,a.verifier_checkpoint)
  C.distinctCheckpoint.call (a.verifier_checkpoint,a.master,a.checkpoint,a.lane,a.registry)
  match a.registry with
  | [registry,entry] =>
    alloc
    let metas := [readonly a.proof,readonly a.master,readonly a.checkpoint,readonly a.lane,readonly registry,readonly entry]
    let metas ← match a.verifier_checkpoint with
      | none => Computation.pure metas
      | some cp => do alloc; Computation.pure (metas ++ [readonly cp])
    alloc
    let infos := [a.proof,a.master,a.checkpoint,a.lane,registry,entry]
    let infos ← match a.verifier_checkpoint with
      | none => Computation.pure (infos ++ [a.verifier_program])
      | some cp => do alloc; Computation.pure (infos ++ [cp,a.verifier_program])
    runtime.clearReturnData
    runtime.invoke ⟨⟨a.plan.selected_verifier,metas,a.plan.request_bytes⟩,infos,[]⟩
    let returned ← runtime.readReturnData
    match returned with
    | none => Computation.throw (.custom 0x4153202f)
    | some (program,data) =>
      check (decide (program ≠ a.plan.selected_verifier)) (.custom 0x4153202c)
      check (data.bytes.length != 792) (.custom 0x4153202d)
      let result ← C.decodeResult.call data.bytes
      alloc
      if data.bytes.length < data.capacity then alloc
      Computation.pure ⟨result,data.bytes⟩
  | _ => Computation.throw (if a.registry.length < 2 then .notEnoughAccountKeys else .invalidArgument)

def RowSpec (C : Children) (runtime : Runtime)
    (impl : Args → State → Env → Observation AuthenticatedResult) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C runtime) impl
end PCM_POOL_348
