import Tx1Q_Cuts
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.Tx1Q_Execution
open Tx1Q_Carriers

def base {CoreError : Type} (ops : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError) :=
  Tx1Q_PrefixInstall.install ops reserved query geo

def actual {CoreError : Type} (ops : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :=
  RowShape_InstalledSlots.verifierOps (Op3I_Install.install (Op4P_Install.install
    (base ops reserved query geo))) B std

structure Slots {CoreError : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError) : Prop where
  initial : installed.op20 = Tx1Q_PrefixInstall.initial reserved
  pending : installed.op18 = Tx1Q_PrefixInstall.newPending reserved
  geometry : installed.op19 = Tx1Q_PrefixInstall.geometryBody geo
  query : installed.op7 = Tx1Q_Install.query (Tx1Q_QueryBridge.leaves query)
  flush : installed.op17 = Tx1Q_Install.flush
  writer : @installed.op16 = @Tx1Q_Install.writer

theorem actual_slots {CoreError : Type} (ops : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls) :
    Slots (actual ops reserved query geo B std) reserved query geo :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

attribute [local irreducible] actual AspisR1CurrentCaller.verifier.candidate.tx1
  AspisR1CurrentCaller.verifier.candidate.prepare
  Port3_NativeQueryBody.verifier.candidate.query_loop
  Port3_Initial.constructor Port3_NativePendingInstall.source
  Port3_GeometryStage.geometry Port3_FlushInstall.flush Port3_CheckpointInstall.writer

/-- All carriers are returned by one accepted TX1. Proof fields are outputs of
success inversion. This record is never an assumption of the accepted theorem. -/
structure Run {CoreError H : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8) where
  p : C.P
  zero : C.E
  scratch : Array C.E 29#usize
  initial : C.A
  root : Array U8 32#usize
  geometry : C.G
  pending : C.B
  out : C.A
  after : C.B
  flushed : Slice C.K
  split_eq : split = 10#usize
  prepare_call : AspisR1CurrentCaller.verifier.candidate.prepare
    installed D semantic proof hash none (Array.repeat 29#usize zero) =
      ok (.Ok p,scratch)
  initial_call : Port3_Initial.constructor reserved .S2 = ok (.Ok (accumulator initial))
  batch_call : installed.op6 D proof p root 0#usize hash = ok (.Ok ())
  geometry_call : Port3_GeometryStage.geometry (Port5Q1_GeometryTerminal.install geo)
    p.queries 0#usize 10#usize = ok (.Ok (Tx1Q_Carriers.geometry geometry))
  pending_call : Port3_NativePendingInstall.source reserved (accumulator initial).weights.deref =
    ok (.Ok (Tx1Q_Carriers.pending pending))
  query_call : Port3_NativeQueryBody.verifier.candidate.query_loop (Tx1Q_QueryBridge.leaves query)
    proof (prepared p) (accumulator initial) (arr e scratch) none (Tx1Q_Carriers.geometry geometry)
    (Tx1Q_Carriers.pending pending) 10#usize = ok (.Ok (accumulator out,Tx1Q_Carriers.pending after))
  flush_call : Port3_FlushInstall.flush (Tx1Q_Carriers.pending after) (accumulator out).weights.deref =
    ok (slice k flushed)
  writer_call : Port3_CheckpointInstall.writer (Tx1Q_Install.digest D) (prepared p)
    (accumulator {out with weights := ⟨flushed.val,flushed.property⟩}) proof pub hash = ok saved

/-- Construct the entire query/flush/writer witness from the actual accepted
call, keeping preparation and the gamma scratch returned by that call. -/
theorem accepted_generic {CoreError H : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (slots : Slots installed reserved query geo)
    (success : AspisR1CurrentCaller.verifier.candidate.tx1 installed
      D semantic pub proof split hash none = ok (.Ok saved)) :
    Nonempty (Run installed reserved query geo D hash semantic pub proof split saved) := by
  obtain ⟨hs,variant,zero,p,scratch,hshape,hscan,hzero,hprep,htail⟩ :=
    AspisR1CurrentCaller.Tx1Reachability.tx1_success _ D semantic pub proof split hash saved success
  have splitEq : split = 10#usize := by
    simpa only [AspisR1CurrentCaller.compact.SPLIT] using hs
  cases splitEq
  obtain ⟨a,root,geometry,b,out,after,flushed,hinit,hbatch,hgeo,hpending,hquery,hflush,hwriter⟩ :=
    Tx1Q_Cuts.suffix _ D pub proof 10#usize hash p scratch saved htail
  rw [slots.initial] at hinit
  rw [slots.pending] at hpending
  rw [slots.geometry] at hgeo
  rw [slots.query] at hquery
  rw [slots.flush] at hflush
  rw [slots.writer] at hwriter
  have init := Tx1Q_PrefixInstall.initial_success reserved a hinit
  have pend := Tx1Q_PrefixInstall.pending_success reserved a.weights.deref b hpending
  have geom := Tx1Q_PrefixInstall.geometry_success geo p.queries 0#usize 10#usize geometry hgeo
  have qry := Tx1Q_Install.query_success (Tx1Q_QueryBridge.leaves query) proof p a out scratch none
    geometry b after 10#usize hquery
  rw [Tx1Q_QueryBridge.release_leaves] at qry
  have fl := Tx1Q_Install.flush_success after out.weights.deref flushed hflush
  exact ⟨⟨p,zero,scratch,a,root,geometry,b,out,after,flushed,rfl,hprep,init,hbatch,geom,pend,qry,fl,hwriter⟩⟩

#print axioms actual_slots
#print axioms accepted_generic
#print Run
end AspisR1.Tx1Q_Execution
end
