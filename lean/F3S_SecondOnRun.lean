import F3S_SecondRoot
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_SecondOnRun
open Aeneas Aeneas.Std Result CheckpointBytes5Effect VTop_Stages
 theorem log {Hash : Type} (base : Ops) (reserved : Bool)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (D : aspis_core.digest.Digest32 Hash)
    (pub proof checkpoint : Slice U8) (hash : Hash)
    (p : verifier.Prepared) (acc : verifier.Accumulator) (root : Array U8 32#usize) (view : Slice U8)
    (reader : erase (SdkC_Source.dictionary hashv) ()
      (GExq_RetainedReader.code reserved checkpoint proof pub .S2)=ok (.Ok (p,acc)))
    (start : (GExq_SecondCode.installed base reserved).op15=ok 7751#usize)
    (finish : (GExq_SecondCode.installed base reserved).op14=ok 7783#usize)
    (unwrap : (GExq_SecondCode.installed base reserved).unwrap32 (.Ok root)=ok root)
    (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=7751#usize,«end»:=7783#usize}=ok view)
    (copy : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view=ok (.Ok root))
    (success : erase (SdkC_Source.dictionary hashv) ()
      (GExq_SecondCode.code base reserved hashv D pub proof checkpoint hash)=ok (.Ok ())) :
    SdkC_Source.readLog (SdkC_Source.run hashv
      (GExq_SecondCode.code base reserved hashv D pub proof checkpoint hash) []).2=
    SdkC_Source.readLog (SdkC_Source.run hashv (GExq_RetainedReader.code reserved checkpoint proof pub .S2) []).2 ++
    SdkC_Source.readLog (SdkC_Source.run hashv (GExq_BatchSource.stage D hash proof p root) []).2 := by
  obtain ⟨p2,a2,root2,read2,batch,⟨off0,off1,view2,raw,h0,h1,range2,copy2,unwrapped⟩,logs⟩ :=
    F3S_SecondRoot.split base reserved hashv D pub proof checkpoint hash success
  have pairEq := core.result.Result.Ok.inj (Result.ok.inj (read2.symm.trans reader))
  have pEq := congrArg Prod.fst pairEq
  have aEq := congrArg Prod.snd pairEq
  dsimp only at pEq aEq
  subst p2
  subst a2
  have off0Eq : off0=7751#usize := Result.ok.inj (h0.symm.trans start)
  have off1Eq : off1=7783#usize := Result.ok.inj (h1.symm.trans finish)
  subst off0
  subst off1
  have viewEq : view2=view := Result.ok.inj (range2.symm.trans range)
  subst view2
  have rawEq : raw=.Ok root := Result.ok.inj (copy2.symm.trans copy)
  subst raw
  have rootEq : root2=root := Result.ok.inj (unwrapped.symm.trans unwrap)
  subst root2
  exact logs
#print axioms log
end AspisR1.F3S_SecondOnRun
end
