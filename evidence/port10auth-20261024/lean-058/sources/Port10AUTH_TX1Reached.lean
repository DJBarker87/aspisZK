import Port10AUTH_TX1Cut

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_TX1Reached
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem accepted (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap) (rest : Implementation)
    {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (pub proof : Slice U8)
    (saved : alloc.vec.Vec U8) (H : Bytes → State)
    (success : (eval H (interpret (Port9OR_Installed.implementation ops reserved unwrap rest)
      (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none))).2=ok (.Ok saved)) :
    let impl : Implementation := Port9OR_Installed.implementation ops reserved unwrap rest
    ∃ p a g folded slice conversion earlier,
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) proof
        {start:=7751#usize,«end»:=7783#usize}=ok slice ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 slice=ok conversion ∧
      ops.unwrap32 conversion=ok folded ∧
      Port4B_Install.batch (Port9OR_Bodies.native D H) proof p folded 0#usize hash=ok (.Ok ()) ∧
      (eval H (interpret impl (Port10AUTH_TX1Cut.afterBatch D pub proof 10#usize hash none p a g (.Ok ())))).2=ok (.Ok saved) ∧
      (eval H (interpret impl (VTop_Flow.tx1 VTop_Flow.traceEffects D semantic pub proof 10#usize hash none))).1=
        earlier ++ (eval H (Port9OR_Installed.batch D hash proof p folded 0#usize)).1 ++
        (eval H (interpret impl (Port10AUTH_TX1Cut.afterBatch D pub proof 10#usize hash none p a g (.Ok ())))).1 := by
  let impl : Implementation := Port9OR_Installed.implementation ops reserved unwrap rest
  rw [← Port10AUTH_TX1Cut.source] at success ⊢
  unfold Port10AUTH_TX1Cut.code at success ⊢
  obtain ⟨i,split,r0,l0⟩ := Port9OR_Driver.head impl _ _ H _ success
  have same : i=10#usize := (Result.ok.inj split).symm
  subst i
  obtain ⟨parsed,parseCall,r1,l1⟩ := Port9OR_Driver.head impl _ _ H _ r0
  cases parsed with
  | Err e => cases r1
  | Ok variant =>
    obtain ⟨checked,checkCall,r2,l2⟩ := Port9OR_Driver.head impl _ _ H _ r1
    cases checked with
    | Err e => cases r2
    | Ok unit =>
      obtain ⟨mark,markCall,r3,l3⟩ := Port9OR_Driver.head impl _ _ H _ r2
      cases mark
      obtain ⟨we,weCall,r4,l4⟩ := Port9OR_Driver.head impl _ _ H _ r3
      obtain ⟨⟨prepared,g⟩,preparedCall,r5,l5⟩ := Port9OR_Driver.head impl _ _ H _ r4
      cases prepared with
      | Err e => cases r5
      | Ok p =>
        obtain ⟨initial,initialCall,r6,l6⟩ := Port9OR_Driver.head impl _ _ H _ r5
        cases initial with
        | Err e => cases r6
        | Ok a =>
          obtain ⟨mark,markCall,r7,l7⟩ := Port9OR_Driver.head impl _ _ H _ r6
          cases mark
          obtain ⟨start,startCall,r8,l8⟩ := Port9OR_Driver.head impl _ _ H _ r7
          have startEq : start=7751#usize := (Result.ok.inj startCall).symm
          subst start
          obtain ⟨finish,finishCall,r9,l9⟩ := Port9OR_Driver.head impl _ _ H _ r8
          have finishEq : finish=7783#usize := (Result.ok.inj finishCall).symm
          subst finish
          obtain ⟨slice,read,r10,l10⟩ := Port9OR_Reached.pure_head impl _ _ H _ r9
          obtain ⟨conversion,array,r11,l11⟩ := Port9OR_Reached.pure_head impl _ _ H _ r10
          obtain ⟨folded,unwrapped,r12,l12⟩ := Port9OR_Driver.head impl _ _ H _ r11
          obtain ⟨out,batchCall,r13,l13⟩ := Port9OR_Driver.head impl _ _ H _ r12
          cases out with
          | Err e => cases r13
          | Ok unit =>
            cases unit
            have native := (Port9OR_Installed.value D hash proof p folded 0#usize H).symm.trans batchCall
            refine ⟨p,a,g,folded,slice,conversion,
              (eval H (impl (.op3 proof))).1 ++ (eval H (impl (.op4 proof))).1 ++
              (eval H (rest (.op7 D semantic proof hash none (Array.repeat 29#usize we)))).1,
              read,array,unwrapped,native,r13,?_⟩
            rw [l0,l1,l2,l3,l4,l5,l6,l7,l8,l9,l10,l11,l12,l13]
            rfl

#print axioms accepted
end AspisR1.Port10AUTH_TX1Reached
end
