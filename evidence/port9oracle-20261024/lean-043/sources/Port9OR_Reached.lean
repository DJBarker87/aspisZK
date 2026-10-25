import Port9OR_BatchCut

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port9OR_Reached
open Aeneas Aeneas.Std Result VTop_Stages VTop_Trace VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem rejected {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator) (i : Usize)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (inactive : aspis_core.field.wide_exact.WideExact) (i2 i3 i4 : Usize)
    (e : verifier.Error) (impl : Implementation) (H : Bytes → State) :
    eval H (interpret impl (Port9OR_BatchCut.afterBatch D proof none p a i g inactive i2 i3 i4 (.Err e)))=
      ([],ok (.Err e)) := rfl

/-- Actual accepted source suffix reaches installed physical op5 on the SAME
p and the actual folded-root unwrap return. Every source decoding/Std error
precedes the call; no root, opening, scratch or successful model run is chosen. -/
theorem after_powers (ops : Ops) (reserved : Bool) (unwrap : Port6CK_Semantic.Unwrap)
    (rest : Implementation) {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator) (i : Usize)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (H : Bytes → State)
    (accepted : (eval H (interpret (Port9OR_Installed.implementation ops reserved unwrap rest)
      (Port8EFF_Control.afterPowers D proof hash none p a i g))).2=ok (.Ok ())) :
    ∃ inactive folded slice conversion,
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) proof
        {start:=7751#usize,«end»:=7783#usize}=ok slice ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 slice=ok conversion ∧
      ops.unwrap32 conversion=ok folded ∧
      Port4B_Install.batch (Port9OR_Bodies.native D H) proof p folded 1#usize hash=ok (.Ok ()) ∧
      (eval H (interpret (Port9OR_Installed.implementation ops reserved unwrap rest)
        (Port9OR_BatchCut.afterBatch D proof none p a i g inactive 7527#usize 7751#usize 7783#usize (.Ok ())))).2=ok (.Ok ()) ∧
      (eval H (interpret (Port9OR_Installed.implementation ops reserved unwrap rest)
        (Port8EFF_Control.afterPowers D proof hash none p a i g))).1=
          (eval H (Port9OR_Installed.batch D hash proof p folded 1#usize)).1 ++
          (eval H (interpret (Port9OR_Installed.implementation ops reserved unwrap rest)
            (Port9OR_BatchCut.afterBatch D proof none p a i g inactive 7527#usize 7751#usize 7783#usize (.Ok ())))).1 := by
  let impl := Port9OR_Installed.implementation ops reserved unwrap rest
  rw [← Port9OR_BatchCut.source] at accepted ⊢
  unfold Port9OR_BatchCut.beforeBatch at accepted ⊢
  obtain ⟨mark,marked,r0,l0⟩ := Port9OR_Driver.head impl _ _ H _ accepted
  cases mark
  obtain ⟨start,started,r1,l1⟩ := Port9OR_Driver.head impl .op23 _ H _ r0
  have startEq : start=7495#usize := (Result.ok.inj started).symm
  subst start
  obtain ⟨finish,finished,r2,l2⟩ := Port9OR_Driver.head impl .op22 _ H _ r1
  have finishEq : finish=7527#usize := (Result.ok.inj finished).symm
  subst finish
  cases range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) proof
      {start:=7495#usize,«end»:=7527#usize} with
  | fail e => simp only [interpret,range,continueWith,eval] at r2; cases r2
  | div => simp only [interpret,range,continueWith,eval] at r2; cases r2
  | ok bytes =>
    simp only [interpret,range,continueWith] at r2
    obtain ⟨option,decoded,r3,l3⟩ := Port9OR_Driver.head impl (.op2 bytes) _ H _ r2
    obtain ⟨parsed,converted,r4,l4⟩ := Port9OR_Driver.head impl (.op0 option .Parse) _ H _ r3
    cases parsed with
    | Err e => cases r4
    | Ok inactive =>
      obtain ⟨start,started,r5,l5⟩ := Port9OR_Driver.head impl .op15 _ H _ r4
      have startEq : start=7751#usize := (Result.ok.inj started).symm
      subst start
      obtain ⟨finish,finished,r6,l6⟩ := Port9OR_Driver.head impl .op14 _ H _ r5
      have finishEq : finish=7783#usize := (Result.ok.inj finished).symm
      subst finish
      cases read : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) proof
          {start:=7751#usize,«end»:=7783#usize} with
      | fail e => simp only [interpret,read,continueWith,eval] at r6;cases r6
      | div => simp only [interpret,read,continueWith,eval] at r6;cases r6
      | ok slice =>
        simp only [interpret,read,continueWith] at r6
        cases array : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 slice with
        | fail e => simp only [interpret,array,continueWith,eval] at r6;cases r6
        | div => simp only [interpret,array,continueWith,eval] at r6;cases r6
        | ok conversion =>
          simp only [interpret,array,continueWith] at r6
          obtain ⟨folded,unwrapped,r7,l7⟩ := Port9OR_Driver.head impl (.unwrap32 conversion) _ H _ r6
          obtain ⟨out,called,r8,l8⟩ := Port9OR_Driver.head impl (.op5 D proof p folded 1#usize hash) _ H _ r7
          cases out with
          | Err e => rw [rejected] at r8;cases r8
          | Ok unit =>
            cases unit
            have nativeCall := called
            rw [Port9OR_Installed.installed,Port9OR_Installed.value] at nativeCall
            refine ⟨inactive,folded,slice,conversion,read,array,unwrapped,nativeCall,r8,?_⟩
            rw [l0,l1,l2]
            simp only [interpret,range,continueWith]
            rw [l3,l4]
            change _ = _
            simp only [interpret,continueWith,eval]
            rw [l5,l6]
            simp only [interpret,read,continueWith,array]
            rw [l7,l8]
            rfl

#print axioms rejected
#print axioms after_powers
end AspisR1.Port9OR_Reached
end
