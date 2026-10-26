import RPz7_Cons_Native
set_option autoImplicit false
noncomputable section
namespace AspisR1.Cons_NativeBuild
open Aeneas Aeneas.Std Result

def Aux {CoreError Hash : Type} (reserved : Bool) (query : Port3_NativeQueryBody.Ops)
    (geo : Port3_NativeGeometryBody.Ops CoreError)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (pub proof checkpoint : Slice U8) (t : Cons_Native.Witness) : Prop :=
  Port4A_ReaderInstall.reader reserved D checkpoint proof pub .S2 hash = ok (.Ok (t.p2,t.saved2)) ∧
  t.saved2.next = 10#usize ∧
  Port3_GeometryStage.geometry (Port5Q1_GeometryTerminal.install geo)
    t.p2.queries t.saved2.next 22#usize = ok (.Ok t.geometry2) ∧
  Port3_NativePendingInstall.source reserved t.saved2.weights.deref = ok (.Ok t.pending2) ∧
  Port3_QueryStage.query (Port4C_RowStd.install (Port5Q1_QueryPorts.install query))
    proof t.p2 t.saved2 t.g2 none t.geometry2 t.pending2 22#usize = ok (.Ok (t.returned2,t.after2)) ∧
  alloc.vec.Vec.deref_mut t.returned2.weights = (t.returned2.weights.deref,t.back2) ∧
  Port3_FlushInstall.flush t.after2 t.returned2.weights.deref = ok t.flushed2

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
      Aux reserved query geo D hash pub proof checkpoint t := by
  obtain ⟨variant,shape,common⟩ := Tx2I_Cuts.authenticated_reached _ D hash pub proof checkpoint none success
  have commonRun : VTop_Stages.verifier.candidate.tx2_common
      (Tx2N_Execution.control (Tx2I_Install.stage base finish) reserved query geo)
      D pub proof checkpoint hash none = ok (.Ok ()) := common
  obtain ⟨p,saved,g,geometry,pending,returned,after,flushed,back,v,
    hr,hnext,hg,hgeo,hpending,hquery,hback,hflush,hfinish⟩ :=
    Tx2N_Execution.common (Tx2I_Install.stage base finish) reserved query geo D hash pub proof checkpoint commonRun
  have native := T2Nat_ReaderJoin.on_run base reserved query D hash checkpoint proof pub p saved hr
  have logs := T2Nat_ReaderEffects.on_run base reserved query D hash checkpoint proof pub p saved hr
  have finishCall : Port4D_FinishInstall.finish finish v p
      {returned with weights := back flushed} none = ok (.Ok ()) := hfinish
  refine ⟨⟨p,saved,g,geometry,pending,returned,after,flushed,back,v⟩,?_,hr,hnext,hgeo,hpending,hquery,hback,hflush⟩
  refine ⟨hr,native.1,native.2.1,native.2.2,logs,hquery,hback,hflush,hfinish,finishCall,?_⟩
  intro Hash' D' hash' before
  exact T2Nat_FinishResult.accepted_effects D' hash' finish v p {returned with weights := back flushed} finishCall before

#print axioms accepted
end AspisR1.Cons_NativeBuild
end
