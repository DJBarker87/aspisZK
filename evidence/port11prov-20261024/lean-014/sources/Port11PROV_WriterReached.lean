import Port11PROV_TX1Reached
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port11PROV_WriterReached
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem accepted (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap) (rest : Implementation)
    {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X) (H : Bytes → State)
    (pub proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (saved : alloc.vec.Vec U8)
    (success : (eval H (interpret (Port9OR_Installed.implementation ops reserved unwrap rest)
      (Port10AUTH_TX1Cut.afterBatch D pub proof 10#usize hash none p a g (.Ok ())))).2=ok (.Ok saved)) :
    ∃ written, Port3_CheckpointInstall.writer (Port9OR_Bodies.native D H) p written proof pub hash=ok saved := by
  let impl : Implementation := Port9OR_Installed.implementation ops reserved unwrap rest
  unfold Port10AUTH_TX1Cut.afterBatch at success
  obtain ⟨cf,branch,r0,_⟩ := Port9OR_Reached.pure_head impl _ _ H _ success
  have eq : cf=core.ops.control_flow.ControlFlow.Continue () := (Result.ok.inj branch).symm
  subst cf
  obtain ⟨mark,marked,r1,_⟩ := Port9OR_Driver.head impl _ _ H _ r0
  cases mark
  obtain ⟨geometry,geo,r2,_⟩ := Port9OR_Driver.head impl _ _ H _ r1
  cases geometry with
  | Err e => cases r2
  | Ok geometry =>
    obtain ⟨cf,branch,r3,_⟩ := Port9OR_Reached.pure_head impl _ _ H _ r2
    have eq : cf=core.ops.control_flow.ControlFlow.Continue geometry := (Result.ok.inj branch).symm
    subst cf
    obtain ⟨pending,pend,r4,_⟩ := Port9OR_Driver.head impl _ _ H _ r3
    cases pending with
    | Err e => cases r4
    | Ok pending =>
      obtain ⟨cf,branch,r5,_⟩ := Port9OR_Reached.pure_head impl _ _ H _ r4
      have eq : cf=core.ops.control_flow.ControlFlow.Continue pending := (Result.ok.inj branch).symm
      subst cf
      obtain ⟨out,query,r6,_⟩ := Port9OR_Driver.head impl _ _ H _ r5
      cases out with
      | Err e => cases r6
      | Ok pair =>
        obtain ⟨cf,branch,r7,_⟩ := Port9OR_Reached.pure_head impl _ _ H _ r6
        have eq : cf=core.ops.control_flow.ControlFlow.Continue pair := (Result.ok.inj branch).symm
        subst cf
        obtain ⟨out,pending⟩ := pair
        obtain ⟨mut,borrow,r8,_⟩ := Port9OR_Reached.pure_head impl _ _ H _ r7
        obtain ⟨weights,flush,r9,_⟩ := Port9OR_Driver.head impl _ _ H _ r8
        obtain ⟨bytes,wrote,r10,_⟩ := Port9OR_Driver.head impl _ _ H _ r9
        obtain ⟨mark,marked,r11,_⟩ := Port9OR_Driver.head impl _ _ H _ r10
        cases mark
        have same : bytes=saved := core.result.Result.Ok.inj (Result.ok.inj r11)
        subst bytes
        exact ⟨_,(Port9OR_Bodies.writer_value D p _ proof pub hash H).symm.trans wrote⟩

#print axioms accepted
end AspisR1.Port11PROV_WriterReached
end
