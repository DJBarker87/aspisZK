import NPR_R22DotSite
import NPR_R22ClaimSite
import NDO_JFw_Row
import NPH_R22ValuesSite
import NPH_R22Gamma
import LIBC_QueryLoop
import NNH_Run5bCurrentShape

set_option autoImplicit false
noncomputable section
namespace AspisR1.NPR_Screens
open Aeneas Aeneas.Std Result AspisR1Stage2

/-! ### Dictionary readings -/

/-- tx2: the op6 query of NJJ_Common is the NFS packet over NJJ_QueryOps.concrete. -/
theorem tx2_query_base : NJJ_Common.query = NHT_PacketOps.query NJJ_QueryOps.concrete 0 0 := rfl

/-- tx2: from a Domain start, NJJ_Common.query runs query_values on Dcon at every step. -/
theorem tx2_query_Dcon (proof : Slice U8) (p : verifier.Prepared) (g : Array SAQ_WideABI.E 29#usize)
    (geo : verifier.QueryGeometry) (a : verifier.Accumulator) (b : verifier.BatchedWeights)
    (obs : Option (VTop_Stages.verifier.Phase → Result Unit))
    (d0 : NFS_QueryInvariant.Domain p 10 22 a b)
    (canonical : NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g)) :
    NJJ_Common.query proof p a g obs geo b 22#usize =
      NHT_ResultPort.action (NFG_QueryLoopDefs.run (fun a' b' =>
        Port3_NativeQueryBody.verifier.candidate.query_values NPH_R22Join094.Dcon proof p a' g none geo b')
        22#usize 12 (.Ok (a, b))) := by
  unfold NJJ_Common.query NHT_PacketOps.query
  rw [NFS_QueryLoopRoot.finite NJJ_QueryOps.concrete proof p g geo 0 0 10 22#usize (by decide)
    canonical 12 (.Ok (a, b)) d0]

/-- tx1 094 loop (LIBC_QueryLoop.model): its child base is NFS_CallerDomains.select LIBC_QueryOps.seed. -/
theorem libc_model_base (a : LIBC_QueryLoop.Args) (x : RSL.Env) :
    LIBC_QueryLoop.model a x = Port3_QueryInstall.result (NFG_QueryLoopDefs.run
      (NFS_QueryLoopRoot.child (NFS_CallerDomains.select LIBC_QueryOps.seed) (LIBC_Bytes.raw a.1)
        (LIBC_QueryLoop.nativeP a) (LIBC_QueryLoop.nativeG a) (LIBC_QueryLoop.geo a) 0 0)
      10#usize 10 (.Ok (LIBC_QueryLoop.nativeA a, LIBC_QueryLoop.pending a))) := rfl

/-- tx1 094 loop: from a Domain start it runs query_values on Dsel at every step. -/
theorem libc_model_Dsel (a : LIBC_QueryLoop.Args) (x : RSL.Env)
    (d0 : NFS_QueryInvariant.Domain (LIBC_QueryLoop.nativeP a) 0 10 (LIBC_QueryLoop.nativeA a)
      (LIBC_QueryLoop.pending a))
    (canonical : NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray (LIBC_QueryLoop.nativeG a))) :
    LIBC_QueryLoop.model a x = Port3_QueryInstall.result (NFG_QueryLoopDefs.run (fun a' b' =>
      Port3_NativeQueryBody.verifier.candidate.query_values NPH_R22Join094.Dsel (LIBC_Bytes.raw a.1)
        (LIBC_QueryLoop.nativeP a) a' (LIBC_QueryLoop.nativeG a) none (LIBC_QueryLoop.geo a) b')
      10#usize 10 (.Ok (LIBC_QueryLoop.nativeA a, LIBC_QueryLoop.pending a))) := by
  rw [libc_model_base]
  rw [NFS_QueryLoopRoot.finite (NFS_CallerDomains.select LIBC_QueryOps.seed) (LIBC_Bytes.raw a.1)
    (LIBC_QueryLoop.nativeP a) (LIBC_QueryLoop.nativeG a) (LIBC_QueryLoop.geo a) 0 0 0 10#usize
    (by decide) canonical 10 (.Ok (LIBC_QueryLoop.nativeA a, LIBC_QueryLoop.pending a)) d0]

/-! ### weights.field call paths -/

theorem dot_record_field : NPR_R22DotSite.R.field = AspisR1CurrentWide.Proof.finishField := rfl

theorem finishField_body (bytes : Slice U8) (i : Usize) :
    AspisR1CurrentWide.Proof.finishField bytes i = (do
      let value ← AspisR1WeightsFieldCurrent.weights.field
        AspisR1RecordParser.field.wide_exact.WideExact.from_le_bytes bytes i
      ok (AspisR1CurrentWide.Proof.recordWideToFinish value)) := rfl

theorem claim_record_field (rawFn : AspisR1EbyKPushDotBackend.RawFn) :
    (AspisR1S5ClaimDotConcreteAdapter.concreteOps rawFn).field = AspisR1CurrentPreparedClaim.ClaimParser.field := rfl

theorem claimParser_body (bytes : Slice U8) (i : Usize) :
    AspisR1CurrentPreparedClaim.ClaimParser.field bytes i = (do
      let x ← AspisR1CurrentWide.Proof.finishField bytes i
      ok (AspisR1CurrentPreparedClaim.ClaimParser.fromFinish x)) := rfl

/-! ### Executed records -/

/-- The record of the deployed adapter is currentInstalled at the host configuration. -/
theorem current_is_installed (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE) (env : RSL.Env)
    (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation) :
    NNH_Run5bCurrentShape.current m env err r =
      DrvC_Installation.currentInstalled (NNH_CorrectConfiguration.configuration m env err r) := rfl

/-- The deployed sampling runs gamma on candidateGammaPublic, i.e. gamma_sample on candidateGammaHelpers. -/
theorem deployed_gamma (S : AspisR1PublicPreparation.PreparedModel.Boundaries)
    (e : AspisR1PublicPreparation.aspis_core.field.M31 → Result AspisR1PublicPreparation.aspis_core.field.WideExact) :
    (AspisR1ClaimPreparedBridge.InstalledMeaning.installedBoundaries S e).gamma =
      AspisR1ClaimPreparedBridge.candidateGammaPublic := by
  rw [AspisR1ClaimPreparedBridge.InstalledMeaning.installed_as_candidate_samplers]
  rfl

theorem candidateGammaPublic_body (block : Array U8 32#usize) :
    AspisR1ClaimPreparedBridge.candidateGammaPublic block = (do
      let out ← AspisR1GammaCaller.sampler.gamma_sample AspisR1GammaCaller.DigitsModel.candidateGammaHelpers block
      ok (AspisR1ClaimPreparedBridge.gammaToPublic out)) := rfl

/-! ### The `?` operator on an Err result -/

theorem question_err {T R E : Type} (e : E) (K : T → Result (core.result.Result R E)) :
    (do
      let cf ← core.result.Result.Insts.CoreOpsTry.branch (core.result.Result.Err e : core.result.Result T E)
      match cf with
      | core.ops.control_flow.ControlFlow.Continue v => K v
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual R
          (core.convert.FromSame E) residual) = ok (core.result.Result.Err e) := rfl

/-! ### The compact expandValues call site -/

section
open ControlFlow AspisS1NativeCompact AspisS1ValuesOwnedInstallation PSem_Iterator

def expandValuesG (payload window : Slice U8) :=
  if payload.val.length ≤ 1856 then expandValues payload window else fail .panic

/-- JFw_Row.runRow with expandValues guarded on the payload length 1856. -/
def runRowG (input out : Slice U8) (nextRow row : U8) (size src dst : Usize) := do
  let i ← dst + 5#usize
  let (s, back) ← core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeUsizeSlice U8) out {start := dst, «end» := i}
  let i1 ← src + 5#usize
  let s1 ← core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeUsizeSlice U8) input {start := src, «end» := i1}
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  let b ← compact.compact_row row
  if b then
    let half ← size / 2#usize
    let sourceEnd ← i1 + half
    let payload ← core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice U8) input {start := i1, «end» := sourceEnd}
    let destEnd ← i + size
    let (window, back1) ← core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice U8) (back s2) {start := i, «end» := destEnd}
    let (status, updated) ← expandValuesG payload window
    let cf ← core.result.Result.Insts.CoreOpsTry.branch status
    match cf with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let sourceNext ← i1 + half
      ok (cont (iter nextRow, back1 updated, sourceNext, destEnd))
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame compact.CodecError) residual
      ok (done (r,back1 updated))
  else
    let destEnd ← i + size
    let (window, back1) ← core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice U8) (back s2) {start := i, «end» := destEnd}
    let sourceEnd ← i1 + size
    let payload ← core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeUsizeSlice U8) input {start := i1, «end» := sourceEnd}
    let updated ← core.slice.Slice.copy_from_slice core.marker.CopyU8 window payload
    ok (cont (iter nextRow,back1 updated,sourceEnd,destEnd))

/-- The compact row calls expandValues only on its payload input[i1, i1 + size/2), whose length is
at most 1856 (NPH_R22Values.compact_site). -/
theorem runRowG_eq (input out : Slice U8) (nextRow row k : U8) (size src dst : Usize)
    (shape : r1_wire.row_shape row = ok (some (k, size))) :
    runRowG input out nextRow row size src dst = AspisR1.JFw_Row.runRow input out nextRow row size src dst := by
  unfold runRowG AspisR1.JFw_Row.runRow
  refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun i _ => ?_)
  refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun sb _ => ?_)
  obtain ⟨s, back⟩ := sb
  refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun i1 _ => ?_)
  refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun s1 _ => ?_)
  refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun s2 _ => ?_)
  refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun b _ => ?_)
  refine ite_congr rfl (fun _ => ?_) (fun _ => rfl)
  refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun half hhalf => ?_)
  refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun sourceEnd hsum => ?_)
  refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun payload hread => ?_)
  refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun destEnd _ => ?_)
  refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun wb _ => ?_)
  obtain ⟨window, back1⟩ := wb
  refine NPR_R22ClaimSite.bind_congr_eq _ _ _ _ ?_ (fun _ => rfl)
  unfold expandValuesG
  rw [if_pos (NPH_R22Values.compact_site input payload row k size i1 half sourceEnd shape hhalf hsum hread).1]

/-- The compact expand loop body (NDO_JFw_Row factor) with the guarded expandValues. -/
theorem compact_body_guarded (input out : Slice U8) (row nextRow tag : U8) (size src dst : Usize)
    (bound : row.val < 27) (next : nextRow.val = row.val + 1)
    (shape : r1_wire.row_shape row = ok (some (tag, size))) :
    compact.expand_semantic_loop.body nativeValues input (iter row) out src dst =
      runRowG input out nextRow row size src dst :=
  (AspisR1.JFw_Row.factor input out row nextRow tag size src dst bound next shape).trans
    (runRowG_eq input out nextRow row tag size src dst shape).symm
end


/-! ### The prepare op11 (expandValues) call site -/

section

theorem ls11 (O : AspisR1CurrentCaller.Ops) (f : type_of% O.op11) :
    AspisR1CurrentCaller.compact.LOGICAL_SEMANTIC { O with op11 := f } = AspisR1CurrentCaller.compact.LOGICAL_SEMANTIC O := by
  unfold AspisR1CurrentCaller.compact.LOGICAL_SEMANTIC; rfl
theorem os11 (O : AspisR1CurrentCaller.Ops) (f : type_of% O.op11) :
    AspisR1CurrentCaller.compact.OFF_SEMANTIC { O with op11 := f } = AspisR1CurrentCaller.compact.OFF_SEMANTIC O := by
  unfold AspisR1CurrentCaller.compact.OFF_SEMANTIC; rfl
theorem oy11 (O : AspisR1CurrentCaller.Ops) (f : type_of% O.op11) :
    AspisR1CurrentCaller.compact.OFF_Y1 { O with op11 := f } = AspisR1CurrentCaller.compact.OFF_Y1 O := by
  unfold AspisR1CurrentCaller.compact.OFF_Y1 AspisR1CurrentCaller.compact.OFF_SEMANTIC; rfl
theorem oi11 (O : AspisR1CurrentCaller.Ops) (f : type_of% O.op11) :
    AspisR1CurrentCaller.compact.OFF_INACTIVE { O with op11 := f } = AspisR1CurrentCaller.compact.OFF_INACTIVE O := by
  unfold AspisR1CurrentCaller.compact.OFF_INACTIVE AspisR1CurrentCaller.compact.OFF_Y1 AspisR1CurrentCaller.compact.OFF_SEMANTIC; rfl

/-- candidate.prepare calls op11 only on proof[OFF_Y1, OFF_INACTIVE). -/
theorem candidate_op11_congr (O : AspisR1CurrentCaller.Ops) (f : type_of% O.op11)
    {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (g : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize)
    (hagree : ∀ (s2 y1 : Slice U8) (a b : Usize), AspisR1CurrentCaller.compact.OFF_Y1 O = ok a → AspisR1CurrentCaller.compact.OFF_INACTIVE O = ok b →
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) proof
        { start := a, «end» := b } = ok s2 → f s2 y1 = O.op11 s2 y1) :
    AspisR1CurrentCaller.verifier.candidate.prepare { O with op11 := f } D pub proof hash obs g =
      AspisR1CurrentCaller.verifier.candidate.prepare O D pub proof hash obs g := by
  unfold AspisR1CurrentCaller.verifier.candidate.prepare
  rw [ls11, os11, oy11, oi11]
  refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun i _ => ?_)
  refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun i1 _ => ?_)
  refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun i2 _ => ?_)
  refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun r _ => ?_)
  refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun r1 _ => ?_)
  refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun cf _ => ?_)
  cases cf with
  | Break residual => rfl
  | Continue val =>
    refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun sd _ => ?_)
    obtain ⟨s, back⟩ := sd
    refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun sp _ => ?_)
    obtain ⟨⟨semantic, y1⟩, back2⟩ := sp
    refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun i3 _ => ?_)
    refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun i4 hi4 => ?_)
    refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun s1 _ => ?_)
    refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun rs _ => ?_)
    obtain ⟨r2, semantic1⟩ := rs
    refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun cf1 _ => ?_)
    cases cf1 with
    | Break residual => rfl
    | Continue u =>
      refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun i5 hi5 => ?_)
      refine NPR_R22WeightsWidth.bind_congr_ok _ _ _ (fun s2 hs2 => ?_)
      exact NPR_R22ClaimSite.bind_congr_eq _ _ _ _ (hagree s2 y1 i4 i5 hi4 hi5 hs2) (fun _ => rfl)

/-- At every installed configuration (so at the deployed record, current_is_installed), the
prepare runs op11 only on a slice of length at most 1856 (NPH_R22ValuesSite.installed_y1_site). -/
theorem installed_op11_guarded {F C : Type} (cfg : DrvC_Installation.Configuration F C)
    {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (obs : Option (AspisR1CurrentCaller.verifier.Phase → Result Unit))
    (g : Array AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact 29#usize) :
    AspisR1CurrentCaller.verifier.candidate.prepare { DrvC_Installation.currentInstalled cfg with
        op11 := fun s y => if s.val.length ≤ 1856 then (DrvC_Installation.currentInstalled cfg).op11 s y
          else fail .panic } D pub proof hash obs g =
      AspisR1CurrentCaller.verifier.candidate.prepare (DrvC_Installation.currentInstalled cfg) D pub proof hash obs g := by
  apply candidate_op11_congr
  intro s2 y1 a b ha hb hs
  have h := (NPH_R22ValuesSite.installed_y1_site cfg proof s2 a b ha hb hs).1
  simp only [h, ↓reduceIte]
end
#print axioms tx2_query_base
#print axioms tx2_query_Dcon
#print axioms libc_model_base
#print axioms libc_model_Dsel
#print axioms dot_record_field
#print axioms finishField_body
#print axioms claim_record_field
#print axioms claimParser_body
#print axioms current_is_installed
#print axioms deployed_gamma
#print axioms candidateGammaPublic_body
#print axioms question_err
#print axioms runRowG_eq
#print axioms compact_body_guarded
#print axioms candidate_op11_congr
#print axioms installed_op11_guarded
end AspisR1.NPR_Screens
