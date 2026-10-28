import NCU_WriterPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCU_DriverDomain
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open DrvC_Installation
attribute [local irreducible] verifier.candidate.prepare verifier.candidate.tx1
structure Prefix (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (hash : H) where
  parsed : transport.Variant
  zero : aspis_core.field.wide_exact.WideExact
  prepared : verifier.Prepared
  scratch : Array aspis_core.field.wide_exact.WideExact 29#usize
  initial : verifier.Accumulator
  root : Array U8 32#usize
  geometry : verifier.QueryGeometry
  pending : verifier.BatchedWeights
  out : verifier.Accumulator
  after : verifier.BatchedWeights
  flushed : Slice aspis_core.field.QM31
  rootView : Slice U8
  shape : ops.op3 proof = ok (.Ok parsed)
  scan : ops.op4 proof = ok (.Ok ())
  zero_call : aspis_core.field.wide_exact.WideExact.ZERO ops = ok zero
  prepare : verifier.candidate.prepare ops D semantic proof hash none
    (Array.repeat 29#usize zero) = ok (.Ok prepared,scratch)
  root_range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    proof {start:=7751#usize,«end»:=7783#usize} = ok rootView
  root_copy : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 rootView = ok (.Ok root)
  initial_call : ops.op20 .S2 = ok (.Ok initial)
  batch : ops.op6 D proof prepared root 0#usize hash = ok (.Ok ())
  geometry_call : ops.op19 prepared.queries 0#usize 10#usize = ok (.Ok geometry)
  pending_call : ops.op18 initial.weights.deref = ok (.Ok pending)
  query : ops.op7 proof prepared initial scratch none geometry pending 10#usize = ok (.Ok (out,after))
  flush : ops.op17 after out.weights.deref = ok flushed

/-- Every reached writer, without assuming the writer returns. -/
theorem prefix_of_reached (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (hash : H)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (start : compact.OFF_FOLDED_ROOT ops = ok 7751#usize)
    (finish : compact.OFF_ROUND1 ops = ok 7783#usize)
    (reached : NCU_WriterPrefix.Reached ops D semantic pub proof split hash p a) :
    split = 10#usize ∧ ∃ cut : Prefix ops D semantic pub proof hash,
      p = cut.prepared ∧ a = {cut.out with weights := ⟨cut.flushed.val,cut.flushed.property⟩} := by
  unfold NCU_WriterPrefix.Reached NCU_WriterPrefix.beforeWriter at reached
  split at reached
  · cases reached
  · rename_i splitCheck
    have same : split = 10#usize := by
      simpa only [compact.SPLIT,bne_iff_ne,not_not] using splitCheck
    cases same
    unfold NCU_PrefixTail.tail at reached
    rw [start,finish] at reached
    repeat' first
    | (solve | cases reached)
    | uncase_result
    | head_reduce reached
    | split at reached
    all_goals
      repeat' casesm (_ × _)
      simp_all only [Prod.fst,Prod.snd]
      have eq := core.result.Result.Ok.inj (Result.ok.inj reached)
      cases eq
      let cut : Prefix ops D semantic pub proof hash :=
        ⟨_,_,_,_,_,_,_,_,_,_,_,_,by assumption,by assumption,by assumption,by assumption,
          by assumption,by assumption,by assumption,by assumption,by assumption,by assumption,
          by assumption,by assumption⟩
      exact ⟨True.intro,cut,rfl,rfl⟩

variable {F C : Type}
open Tx1Q_Carriers
open NCT_DriverDomain (writerPrepared writerAccumulator)

/-- Control/flush invariants do not depend on the writer returning. Child
constructor, loop and flush facts are imported, not reproved. -/
theorem control (c : Configuration F C)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (cut : Prefix (currentInstalled c) (currentDigest c) semantic pub proof ()) :
    (writerAccumulator cut.out cut.flushed).weights.val.length = 64 ∧
    (writerAccumulator cut.out cut.flushed).next.val = 10 ∧
    ∀ x ∈ (slice k cut.flushed).val, Port3_FlushInstall.Canonical x := by
  have initCall := Tx1Q_PrefixInstall.initial_success c.reserved cut.initial cut.initial_call
  have init := Tx1Q_Initial.fields c.reserved (accumulator cut.initial) initCall
  have pendCall := Tx1Q_PrefixInstall.pending_success c.reserved cut.initial.weights.deref cut.pending cut.pending_call
  have pend := Port3_NativePendingInstall.accepted_fields c.reserved
    (accumulator cut.initial).weights.deref (pending cut.pending) init.1 pendCall
  have qry := Tx1Q_Install.query_success (Tx1Q_QueryBridge.leaves c.query) proof cut.prepared
    cut.initial cut.out cut.scratch none cut.geometry cut.pending cut.after 10#usize cut.query
  rw [Tx1Q_QueryBridge.release_leaves] at qry
  have native : Port3_NativeQueryBody.verifier.candidate.query_loop
      (Port3_NativeRowFrame.install (Tx1Q_QueryBridge.leaves c.query)) proof (prepared cut.prepared)
      (accumulator cut.initial) (arr e cut.scratch) none (geometry cut.geometry)
      (pending cut.pending) 10#usize = ok (.Ok (accumulator cut.out,pending cut.after)) := qry
  have frame := Port3_NativeQueryRaw.loop_raw (Tx1Q_QueryBridge.leaves c.query) proof (prepared cut.prepared)
    (accumulator cut.initial) (accumulator cut.out) (arr e cut.scratch) none (geometry cut.geometry)
    (pending cut.pending) (pending cut.after) 10#usize init.1 pend.2.2.2 (by rw [init.2.1]; decide) native
  have size : (accumulator cut.out).weights.val.length = 64 := by rw [frame.1]; exact init.1
  have lengths : (accumulator cut.out).weights.deref.val.length ≤ (pending cut.after).raw.val.length := by
    change (accumulator cut.out).weights.val.length ≤ (pending cut.after).raw.val.length
    rw [size,frame.2.1]
  have fl := Tx1Q_Install.flush_success cut.after cut.out.weights.deref cut.flushed cut.flush
  have contents := Port3_FlushInstall.accepted_contents (pending cut.after)
    (accumulator cut.out).weights.deref (slice k cut.flushed) lengths fl
  have canon := Port3_FlushInstall.accepted_canonical (pending cut.after)
    (accumulator cut.out).weights.deref (slice k cut.flushed) lengths fl
  refine ⟨?_,frame.2.2,canon⟩
  have len := contents.2.trans size
  simpa only [writerAccumulator,CheckpointBytes3Namespaces.toAccumulator,
    CheckpointBytes3Namespaces.mapVec,Tx1Q_Carriers.accumulator,Tx1Q_Carriers.vec,
    slice,List.length_map] using len

/-- Actual successful writer calls give the accepted-cut class. Failed or
diverging writer calls retain Prefix and control; no fake acceptance is added. -/
theorem accepted_when_writer_returns (c : Configuration F C)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (p : verifier.Prepared) (a : verifier.Accumulator)
    (reached : NCU_WriterPrefix.Reached (currentInstalled c) (currentDigest c)
      semantic pub proof split () p a) (saved : alloc.vec.Vec U8)
    (write : (currentInstalled c).op16 (currentDigest c) p a proof pub () = ok saved) :
    verifier.candidate.tx1 (currentInstalled c) (currentDigest c)
      semantic pub proof split () none = ok (.Ok saved) := by
  rw [NCU_WriterPrefix.resume _ _ _ _ _ _ _ _ _ reached,write,bind_tc_ok]

open CheckpointBytes5Writer CheckpointBytes5Join CheckpointBytesBody CheckpointBytesBlocks

/-- Exact remaining pointwise field gates on an arbitrary reached prefix.
This theorem does NOT claim those gates have been discharged. -/
theorem domain (c : Configuration F C)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (cut : Prefix (currentInstalled c) (currentDigest c) semantic pub proof ())
    (variant : (writerPrepared cut.prepared).variant = .S2)
    (qb : ∀ j : Fin 22,
      ((writerPrepared cut.prepared).queries.val[j.val]'(by simpa [(writerPrepared cut.prepared).queries.property] using j.isLt)).val < 262144)
    (canonical : NCT_DriverDomain.NonWeightCanonical (fields (writerPrepared cut.prepared)
      (writerAccumulator cut.out cut.flushed) (control c semantic pub proof cut).1 qb)) :
    KNE_Caller.WriterDomain (writerPrepared cut.prepared) (writerAccumulator cut.out cut.flushed) := by
  refine ⟨variant,(control c semantic pub proof cut).1,qb,?_,(control c semantic pub proof cut).2.1⟩
  refine ⟨canonical.gamma,canonical.kappa,canonical.alpha,canonical.rho,canonical.semanticAlpha,
    canonical.coordinates,canonical.claim,canonical.rhs,canonical.power,?_⟩
  intro j
  have bound : j.val < cut.flushed.val.length := by
    have len := (control c semantic pub proof cut).1
    simp only [writerAccumulator,CheckpointBytes3Namespaces.toAccumulator,
      CheckpointBytes3Namespaces.mapVec,Tx1Q_Carriers.accumulator,Tx1Q_Carriers.vec,
      List.length_map] at len
    rw [len]
    exact j.isLt
  have hc := (control c semantic pub proof cut).2.2
    (Tx1Q_Carriers.k (cut.flushed.val[j.val]))
    (List.mem_map.mpr ⟨cut.flushed.val[j.val],List.getElem_mem bound,rfl⟩)
  simpa only [fields,writerAccumulator,CheckpointBytes3Namespaces.toAccumulator,
    CheckpointBytes3Namespaces.mapVec,Tx1Q_Carriers.accumulator,Tx1Q_Carriers.vec,
    List.getElem_map,CheckpointBytes3Namespaces.toK,Tx1Q_Carriers.k,
    OraclePortCkptAbi4Decode.Canonical,Port3_FlushInstall.Canonical] using hc

section Leaf
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open CheckpointBytes5Effect CheckpointBytes5Inputs CheckpointBytesDigest MultiproofConeCanonical
open KNE_Model KNE_Composition
open AspisR1Stage2.WireTx2 (singletonParts checksumParts)
variable (c : Configuration F C)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (cut : Prefix (currentInstalled c) (currentDigest c) semantic pub proof ())
    (variant : (writerPrepared cut.prepared).variant = .S2)
    (qb : ∀ j : Fin 22,
      ((writerPrepared cut.prepared).queries.val[j.val]'(by simpa [(writerPrepared cut.prepared).queries.property] using j.isLt)).val < 262144)
    (canonical : NCT_DriverDomain.NonWeightCanonical (fields (writerPrepared cut.prepared)
      (writerAccumulator cut.out cut.flushed) (control c semantic pub proof cut).1 qb))
local notation "wp" => writerPrepared cut.prepared
local notation "wa" => writerAccumulator cut.out cut.flushed
local notation "wd" => domain c semantic pub proof cut variant qb canonical
/-- Same-input leaf on any reached Prefix, with the exact three remaining
field obligations visible. No writer success or accepted suffix is required. -/
theorem leaf
    (H : Bytes → State) (oracle : Oracle (VTop_Checkpoint.digest (Tx1Q_Install.digest (currentDigest c))) () H)
    (native : Bytes → Bytes → Bytes → Prop)
    (valid : LocalCorrect native KND_Schedule.schedule)
    (hp hu hc : Digest) (body out : Slice U8) (before : Log)
    (tr : Trace native (bodyEmissions (fields wp wa wd.size wd.queriesBound)
      (stateOf hp) (stateOf hu)) [] (bytesOf body.val))
    (checksumWrite : native (bytesOf body.val) (bytesOf hc.val) (bytesOf out.val))
    (proofCall : (VTop_Checkpoint.digest (Tx1Q_Install.digest (currentDigest c))).digest () (singletonParts proof) = ok hp)
    (publicCall : (VTop_Checkpoint.digest (Tx1Q_Install.digest (currentDigest c))).digest () (singletonParts pub) = ok hu)
    (checksumCall : (VTop_Checkpoint.digest (Tx1Q_Install.digest (currentDigest c))).digest () (checksumParts body) = ok hc) :
    out.val.length = 1768 ∧
    out = LPm_CheckpointProgram.returned wp wa wd.size wd.queriesBound
      wd.canonical wd.next hp hu hc ∧
    run (VTop_Checkpoint.digest (Tx1Q_Install.digest (currentDigest c))) () (writer wp wa proof pub) before =
      ok (out,((before ++ [(singletonParts proof,hp)]) ++
        [(singletonParts pub,hu)]) ++ [(checksumParts body,hc)]) ∧
    bytesOf out.val = OraclePortCheckpointAbiC5.encode H (bytesOf proof.val) (bytesOf pub.val)
      (CheckpointBytesBlocks.prepared (fields wp wa wd.size wd.queriesBound) wd.canonical)
      (CheckpointBytesBlocks.accumulator (fields wp wa wd.size wd.queriesBound) wd.canonical) := by
  exact KNE_Leaf.native_result (VTop_Checkpoint.digest (Tx1Q_Install.digest (currentDigest c)))
    () H oracle native valid wp wa wd proof pub hp hu hc body out before tr checksumWrite
    proofCall publicCall checksumCall
end Leaf
#print axioms leaf

#print axioms domain

#print axioms control
#print axioms accepted_when_writer_returns

#print axioms prefix_of_reached
end AspisR1.NCU_DriverDomain
end
