import SAG_CommonFull
import SAG_ViewTail
import Cons_NativeBuild
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAG_NativeFull
open Aeneas Aeneas.Std Result

/-- Positions and byte reads retained for the SAME native finish witness. -/
def Shape (ops : VTop_Stages.Ops) (proof : Slice U8) (t : Cons_Native.Witness) : Prop :=
  ∃ (round0 folded round1 finalStart queryStart : Usize),
    ops.op22 = ok round0 ∧ ops.op15 = ok folded ∧ ops.op14 = ok round1 ∧
    ops.op21 = ok finalStart ∧ ops.op20 = ok queryStart ∧
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=round0,«end»:=folded} = ok t.v2.round0 ∧
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=round1,«end»:=finalStart} = ok t.v2.round1 ∧
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=finalStart,«end»:=queryStart} = ok t.v2.final_message

theorem accepted {F C Hash : Type} (base : VTop_Stages.Ops)
    (finish : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8)
    (success : VTop_Stages.verifier.candidate.tx2_authenticated
      (Tx2I_Install.stage (Tx2N_Execution.control base reserved query geo) finish)
      D pub proof checkpoint hash none = ok (.Ok ())) :
    ∃ t : Cons_Native.Witness,
      Cons_Native.Calls base finish reserved query geo D hash pub proof checkpoint t ∧
      Cons_NativeBuild.Aux reserved query geo D hash pub proof checkpoint t ∧
      Shape (Tx2N_Execution.control (Tx2I_Install.stage base finish) reserved query geo) proof t := by
  obtain ⟨variant,shape,common⟩ := Tx2I_Cuts.authenticated_reached _ D hash pub proof checkpoint none success
  have commonRun : VTop_Stages.verifier.candidate.tx2_common
      (Tx2N_Execution.control (Tx2I_Install.stage base finish) reserved query geo)
      D pub proof checkpoint hash none = ok (.Ok ()) := common
  obtain ⟨p,saved,g,geometry,pending,returned,after,inactive,split,r0at,folded,r1at,
    hr,hsplit,hnext,hg,hgeo,hpending,hquery,h0,hfold,h1,tail⟩ :=
    SAG_CommonFull.reached _ D hash pub proof checkpoint none commonRun
  obtain ⟨flushed,back,r0,r1,fm,finalStart,queryStart,hback,hflush,hf,hq,read0,read1,readf,hfinish⟩ :=
    SAG_ViewTail.reached _ proof p none inactive r0at folded r1at (returned,after) tail
  have splitEq : split = 10#usize := (Result.ok.inj hsplit).symm
  have next : saved.next = 10#usize := hnext.trans splitEq
  have native := T2Nat_ReaderJoin.on_run base reserved query D hash checkpoint proof pub p saved hr
  have logs := T2Nat_ReaderEffects.on_run base reserved query D hash checkpoint proof pub p saved hr
  let v := SAG_ViewTail.view inactive r0 r1 fm
  have finishCall : Port4D_FinishInstall.finish finish v p {returned with weights := back flushed} none = ok (.Ok ()) := hfinish
  refine ⟨⟨p,saved,g,geometry,pending,returned,after,flushed,back,v⟩,?_,?_,?_⟩
  · refine ⟨hr,native.1,native.2.1,native.2.2,logs,hquery,hback,hflush,hfinish,finishCall,?_⟩
    intro Hash' D' hash' before
    exact T2Nat_FinishResult.accepted_effects D' hash' finish v p {returned with weights := back flushed} finishCall before
  · exact ⟨hr,next,hgeo,hpending,hquery,hback,hflush⟩
  · exact ⟨r0at,folded,r1at,finalStart,queryStart,h0,hfold,h1,hf,hq,read0,read1,readf⟩

#print axioms accepted
end AspisR1.SAG_NativeFull
end
