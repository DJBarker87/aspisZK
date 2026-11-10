import NOC_Run5bHost
import NOC_SemConv
import NNH_Run5bCurrentShape
import NNH_Run5bCurrentInitial
import NNV_CurrentScan
import NNV_CurrentGeometry
import NNV_CurrentQuerySource
import NNV_CurrentFlush
import NNV_CurrentCheckpoint
import NNV_PrepareView
set_option autoImplicit false
noncomputable section
/-! PCVP_ corrected-seed re-statement of the existing installed-op = library-model correspondences for the
current CurrentCompact Ops at the headline's host context NOC_HostCtx / NOC_HostSeed.m0.
Nothing here is new mathematics: each theorem is an existing NNV_/NNH_ theorem, instantiated at
m := NOC_HostSeed.m0 (envOf c).reservation (defeq to the NOC configuration, probe PCVP_L008) and stated at
`curN c = currentInstalled (NOC_HostCtx.configuration c)`.  Domain per theorem = its own hypotheses.
These relate the installed op to the LIBRARY MODEL (LIB_/LIBC_), not to the frozen emission of the callee. -/
namespace AspisR1.PCVP_NocSlots
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NNH_Libraries

abbrev curN {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :=
  DrvC_Installation.currentInstalled (NOC_HostCtx.configuration c)
abbrev M {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) := NOC_HostSeed.m0 (NNH_HostCtx.envOf c).reservation

/-- Seed identification: the NOC current Ops are the seed-generic `current` at the corrected seed. -/
theorem cur_eq {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
    curN c = NNH_Run5bCurrentShape.current (M c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation := rfl

/-- op3 parse_shape: library parse ok => installed parse returns Ok. -/
theorem op3 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (proof : Slice U8)
    (success : LIB_VLib.parseShapeValue (LIB_Carriers.bytes proof) (NNH_HostCtx.envOf c) = .ok ()) :
    ∃ variant, (curN c).op3 proof = .ok (.Ok variant) :=
  NNH_Run5bCurrentShape.parse (M c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation proof success

/-- op4 canonical_scan: installed = library canonical scan on 57607-byte proofs. -/
theorem op4 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (proof : Slice U8) (width : proof.val.length = 57607) :
    (curN c).op4 proof = .ok (if LIBC_CanonicalScan.good (LIB_Carriers.bytes proof) then .Ok () else .Err .Parse) :=
  NNV_CurrentScan.source (M c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation proof width

/-- op5 wide_view: library view ok => installed view returns the same view. -/
theorem op5 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (proof semantic y1 : Slice U8) (v : VL.View)
    (width : proof.val.length = 57607) (ls : semantic.val.length = 13831) (ly : y1.val.length = 928)
    (called : LIB_VLib.wideViewValue (LIB_Carriers.bytes proof, LIB_Carriers.bytes semantic, LIB_Carriers.bytes y1)
      (NNH_HostCtx.envOf c) = .ok v) :
    (curN c).op5 proof semantic y1 = .ok (.Ok (NNV_PreparedInputs.view v)) :=
  NNV_PrepareView.returned (M c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation proof semantic y1 v width ls ly called

/-- op7 query_loop: installed = the native query body over carriers (to the native body, not yet the library evaluator). -/
theorem op7 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (proof : Slice U8) (p : verifier.Prepared)
    (a : verifier.Accumulator) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (geo : verifier.QueryGeometry) (pending : verifier.BatchedWeights) (stop : Usize) :
    (curN c).op7 proof p a g none geo pending stop =
    Tx1Q_Install.result (fun x : Tx1Q_Carriers.S.A × Tx1Q_Carriers.S.B =>
      (Tx1Q_Carriers.unAccumulator x.1, Tx1Q_Carriers.unPending x.2))
      (Port3_NativeQueryBody.verifier.candidate.query_loop
        (Tx1Q_QueryBridge.leaves (NNH_CorrectConfiguration.configuration (M c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation).query)
        proof (Tx1Q_Carriers.prepared p) (Tx1Q_Carriers.accumulator a)
        (Tx1Q_Carriers.arr Tx1Q_Carriers.e g) none (Tx1Q_Carriers.geometry geo)
        (Tx1Q_Carriers.pending pending) stop) :=
  NNV_CurrentQuerySource.source (M c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation proof p a g geo pending stop

/-- op16 checkpoint writer: installed = library checkpoint output on the carrier image of the arguments. -/
theorem op16 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (a : LIBC_Checkpoint.Args) :
    (curN c).op16 (NNV_PreparedAtHost.digest c)
      (InstalledPreparation.currentPrepared a.1)
      (Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc a.2.1))
      (LIBC_Bytes.raw a.2.2.1) (LIBC_Bytes.raw a.2.2.2) () =
    .ok (⟨(LIBC_Checkpoint.output a (NNH_HostCtx.envOf c)).val,
      (LIBC_Checkpoint.output a (NNH_HostCtx.envOf c)).property⟩ : alloc.vec.Vec U8) :=
  NNV_CurrentCheckpoint.source c a

/-- op17 BatchedWeights::finish: installed = native flush output on the finish domain. -/
theorem op17 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (a : LIBC_Finish.Args) (domain : LIBC_Finish.Domain a) :
    (curN c).op17 (Tx1Q_Carriers.unPending a.1)
      (Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc a.2)).weights.deref =
    .ok (Tx1Q_Carriers.slice Tx1Q_Carriers.unK (NJJ_Flush.output a.1)) :=
  NNV_CurrentFlush.returned c a domain

/-- op19 QueryGeometry::for_range: installed = library geometry model, topResult-wrapped. -/
theorem op19 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (p : LIB_VCarriers.Prepared) (start stop : Nat) :
    (curN c).op19 p.queries (LIBC_Usize.raw start) (LIBC_Usize.raw stop) =
    Tx1Q_PrefixInstall.topResult Tx1Q_PrefixInstall.unGeometry
      (LIBC_Geometry.model (p, start, stop) (NNH_HostCtx.envOf c)) :=
  NNV_CurrentGeometry.source (M c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation p start stop

/-- op20 Accumulator::new: library accumulator ok => installed constructor returns its carrier image. -/
theorem op20 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (a : VL.Acc)
    (called : LIB_VLib.accNewValue () (NNH_HostCtx.envOf c) = .ok a) :
    ∃ native : AspisR1Stage2.verifier.Accumulator,
      Port3_Initial.constructor (NNH_HostCtx.envOf c).reservation .S2 = .ok (.Ok native) ∧
      a = LIBC_VStateCarriers.fromAcc native ∧
      (curN c).op20 .S2 = .ok (.Ok (Tx1Q_Carriers.unAccumulator native)) :=
  NNH_Run5bCurrentInitial.returned (M c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation a called

#print axioms cur_eq
#print axioms op3
#print axioms op4
#print axioms op5
#print axioms op7
#print axioms op16
#print axioms op17
#print axioms op19
#print axioms op20
end AspisR1.PCVP_NocSlots
end
