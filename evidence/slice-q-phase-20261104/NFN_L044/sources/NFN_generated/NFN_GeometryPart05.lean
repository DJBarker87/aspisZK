import Lean
import NFN_PhaseTransport
import NFN_ReserveOwner
import NFN_GeometryPart04
import NFN_GeometryPart03
import NFN_GeometryPart02
import NEB_PureFrame
import NEO_TailRef.Funs
import Port4B_Opening
import Port4C_PrefixMeaning
import Port4C_BatchInverse
import KMX_CopyMeaning

-- BEGIN copied NEW_GeometryContextGeneric: evidence/slice-q-compose4-20261104/NEW_GeometryContextGeneric.lean
set_option autoImplicit false
namespace NFN_NEW_GeometryContextGeneric
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NFN_NEW_GeometryRawBody
variable {CE : Type}

def replace (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32) : Port3_NativeGeometryBody.Ops CE :=
  {o with op8:=sub,op10:=double}

theorem reverse (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32)
    (it : core.iter.adapters.rev.Rev (core.ops.range.Range Usize))
    (flat pref : alloc.vec.Vec U32) (suffix : U32) (inv : alloc.vec.Vec U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0 (replace o sub double) it flat pref suffix inv =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0_loop0 o it flat pref suffix inv := by rfl

theorem zero_callback (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool (replace o sub double) =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool o := by rfl

theorem collect_callback (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 (replace o sub double) =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_4.Insts.CoreOpsFunctionFnMutTupleUsizeArrayM315 o := by rfl

theorem error_callback0 (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError (replace o sub double) =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure.Insts.CoreOpsFunctionFnOnceTupleErrorError o := by rfl

theorem error_callback1 (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError (replace o sub double) =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError o := by rfl

theorem error_callback2 (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError (replace o sub double) =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range.closure_2.Insts.CoreOpsFunctionFnOnceTupleErrorError o := by rfl

/-- Generic one-body congruence. Its sole arithmetic premise is a contextual
three-call law, later discharged without a parent-success assumption. -/
theorem step (o : Port3_NativeGeometryBody.Ops CE) (sub : U32 → U32 → Result U32)
    (double : U32 → Result U32)
    (poly : ∀ (T : Type) (x : U32) (k : U32 → Result T),
      (do let p ← o.op9 x x; let d ← double p; let one ← o.op7; let z ← sub d one; k z) =
      (do let p ← o.op9 x x; let d ← o.op10 p; let one ← o.op7; let z ← o.op8 d one; k z))
    (start : Usize) (iter : core.slice.iter.Iter U32) (lines flat : alloc.vec.Vec U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body (replace o sub double) start iter lines flat =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body o start iter lines flat := by
  simp only [Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body,
    reverse,zero_callback,collect_callback,error_callback0,error_callback1,error_callback2]
  simp only [replace,bind_assoc_eq,bind_tc_ok]
  conv_lhs =>
    pattern (o.op9 _ _ >>= _)
    rw [poly]

#print axioms replace
#print axioms reverse
#print axioms zero_callback
#print axioms collect_callback
#print axioms error_callback0
#print axioms error_callback1
#print axioms error_callback2
#print axioms step
end NFN_NEW_GeometryContextGeneric
-- END copied NEW_GeometryContextGeneric
-- BEGIN copied NEW_GeometryContext: evidence/slice-q-compose4-20261104/NEW_GeometryContext.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NEW_GeometryContext
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NFN_NEW_GeometryRawInterface NFN_NEW_GeometryRawBody NFN_NEW_GeometryDictionary
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20


theorem one : adopted.op7=ok 1#u32 := by rfl
 theorem multiply : adopted.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul := by rfl
 theorem double : adopted.op10=AspisR1Qm31ArithmeticProbe.field.M31.double := by rfl
 theorem subtract : adopted.op8=AspisR1Qm31ArithmeticProbe.field.M31.sub := by rfl

theorem polynomial {T : Type} (x : U32) (k : U32 → Result T) :
 (do let p ← adopted.op9 x x
     let d ← ops.op10 p
     let one ← adopted.op7
     let z ← ops.op8 d one
     k z) =
 (do let p ← adopted.op9 x x
     let d ← adopted.op10 p
     let one ← adopted.op7
     let z ← adopted.op8 d one
     k z) := by
 simp only [one,multiply,double,subtract,ops,bind_tc_ok]
 simpa only [NFN_NEW_GeometryArithmetic.multiply_probe,NEW_GeometryActual.aspis_core.field.M31.ONE] using NFN_NEW_GeometryPolynomial.continuation x k

/-- Contextual replacement of only the two operations whose unrestricted raw
input specifications differ. The preceding product establishes their domains. -/
theorem step (start : Usize) (iter : core.slice.iter.Iter U32) (lines flat : alloc.vec.Vec U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body contextual start iter lines flat =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted start iter lines flat := by
  exact NFN_NEW_GeometryContextGeneric.step adopted ops.op8 ops.op10
    (fun T x k => polynomial x k) start iter lines flat

#print axioms one
#print axioms multiply
#print axioms double
#print axioms subtract
#print axioms polynomial
#print axioms step
end NFN_NEW_GeometryContext
end
-- END copied NEW_GeometryContext
-- BEGIN copied NEW_GeometryComplete: evidence/slice-q-compose4-20261104/NEW_GeometryComplete.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NEW_GeometryComplete
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NFN_NEW_GeometryRawInterface NFN_NEW_GeometryDictionary
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

theorem step (start : Usize) (iter : core.slice.iter.Iter U32) (lines flat : alloc.vec.Vec U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body ops start iter lines flat =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted start iter lines flat := by
  rw [dictionary]
  exact NFN_NEW_GeometryContext.step start iter lines flat

theorem complete_loop (iter : core.slice.iter.Iter U32) (start : Usize) (lines flat : alloc.vec.Vec U32) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0 ops iter start lines flat =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0 adopted iter start lines flat := by
  simp only [Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0,step]

theorem adopted_root (queries : Array U32 22#usize) (start finish : Usize) :
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range ops queries start finish =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range adopted queries start finish := by
  simp only [Port3_NativeGeometryBody.verifier.QueryGeometry.for_range,complete_loop]

/-- Universal full Result correspondence with the adopted cohort root.
There is no parent-success, child-output, domain or inner-bridge premise. -/
theorem complete_raw (queries : Array U32 22#usize) (start finish : Usize) :
    resultMap answer (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish) =
    Port3_NativeGeometryBody.verifier.QueryGeometry.for_range adopted queries start finish := by
  exact (NFN_NEW_GeometryRawRoot.complete queries start finish).trans (adopted_root queries start finish)

/-- Apply the existing lossless error-name transport to the headline cohort interface. -/
theorem complete (queries : Array U32 22#usize) (start finish : Usize) :
    Port3_QueryInstall.result
      (resultMap answer (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish)) =
    Port3_GeometryStage.geometry adopted queries start finish := by
  unfold Port3_GeometryStage.geometry
  rw [complete_raw]

/-- Persistent state is unchanged; the complete successful geometry and every
rejection/failure/divergence are retained in the result component. Physical
allocation/copy observations are a separate native packet. -/
theorem result_state {State : Type} (queries : Array U32 22#usize) (start finish : Usize) (state : State) :
    (Port3_QueryInstall.result (resultMap answer (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish)),state) =
    (Port3_GeometryStage.geometry adopted queries start finish,state) := by
  rw [complete]

/-- The caller's nonempty successful geometry has exactly the adopted flat
order, canonical nonzero operands, SAME-vector reciprocal cells and all five
collected lanes. Acceptance is the root result being characterized. -/
theorem accepted (queries : Array U32 22#usize) (start finish : Usize)
    (out : AspisR1Stage2.verifier.QueryGeometry) (nonempty : start.val<finish.val)
    (run : Port3_QueryInstall.result
      (resultMap answer (NEW_GeometryActual.verifier.QueryGeometry.for_range queries start finish))=ok (.Ok out)) :
    ∃ flat inverse : alloc.vec.Vec U32,
      out.start=start ∧ out.line_z.val.length=finish.val-start.val ∧
      flat.val.length=5*(finish.val-start.val) ∧
      (∀ x ∈ flat.val, Port5Q1_GeometryCanonical.Canonical x) ∧
      (∀ x ∈ flat.val, S7JoinBasisMachine.decode x≠0) ∧
      inverse.val.length=flat.val.length ∧
      (∀ j, j<flat.val.length →
        S7JoinBasisMachine.decode (Port4C_BatchInverse.cell inverse.val j)=
          (S7JoinBasisMachine.decode (Port4C_BatchInverse.cell flat.val j))⁻¹) ∧
      out.inverses.val=(List.range (finish.val-start.val)).map (Port4C_CollectLoop.record inverse) := by
  rw [complete] at run
  exact NFN_NEB_ActualGeometryModel.for_range ops err queries start finish out nonempty run

#print axioms step
#print axioms complete_loop
#print axioms adopted_root
#print axioms complete_raw
#print axioms complete
#print axioms result_state
#print axioms accepted
end NFN_NEW_GeometryComplete
end
-- END copied NEW_GeometryComplete
-- BEGIN copied NFB_GeometryInstall: evidence/slice-q-compose5-20261104/NFB_GeometryInstall.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NFB_GeometryInstall
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open NFN_NEW_GeometryRawInterface NFN_NEW_GeometryDictionary
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

/-- Reinstalling std in the already adopted dictionary changes nothing. -/
theorem standard : Port4C_GeometryStd.install adopted=adopted := by rfl

/-- Every emitted one-step Result uses the SAME iterator and both evolving
vectors; contextual arithmetic substitution has no free child premise. -/
theorem step (start : Usize) (iter : core.slice.iter.Iter U32)
    (lines flat : alloc.vec.Vec U32) :
 resultMap (NFN_NEW_LoopMap.flowMap answer)
   (NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0.body start iter lines flat)=
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0.body adopted start iter lines flat :=
 (NFN_NEW_GeometryRawBody.step start iter lines flat).trans
   (NFN_NEW_GeometryComplete.step start iter lines flat)

/-- Whole partial Result, including all rejection/failure/divergence branches.
The native physical packet is separately checked by the hybrid validator. -/
theorem loop (start : Usize) (iter : core.slice.iter.Iter U32)
    (lines flat : alloc.vec.Vec U32) :
 resultMap answer (NEW_GeometryActual.verifier.QueryGeometry.for_range_loop0 iter start lines flat)=
 Port3_NativeGeometryBody.verifier.QueryGeometry.for_range_loop0 adopted iter start lines flat :=
 (NFN_NEW_GeometryRawRoot.complete_loop start iter lines flat).trans
   (NFN_NEW_GeometryComplete.complete_loop iter start lines flat)

#print axioms standard
#print axioms step
#print axioms loop
end NFN_NFB_GeometryInstall
end
-- END copied NFB_GeometryInstall
-- BEGIN copied NBG_SquareTrace: lean/NBG_SquareTrace.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NBG_SquareTrace
open Aeneas Aeneas.Std Result ControlFlow AspisR1
open AspisR1M31Inverse.SquareProof

/-- Native cells supply only the paired scalar natural-value relation, not a
model return or a whole-function output equality. K028 constructs each step. -/
inductive Trace : Nat → U32 → U32 → Prop
  | done (value : U32) : Trace 0 value value
  | step {n : Nat} {before middle after : U32}
      (cell : middle.val = (before.val*before.val)%2147483647)
      (tail : Trace n middle after) : Trace (n+1) before after

theorem loop_result {n : Nat} {before after : U32}
    (trace : Trace n before after) (iter : core.ops.range.Range Usize)
    (count : iter.end.val-iter.start.val=n) :
    AspisR1M31Inverse.field.square_n_loop FIo_Native.aspis_core.field.M31.mul
      iter before = ok after := by
  induction trace generalizing iter with
  | done value =>
    have stopped : iter.start.val ≥ iter.end.val := by omega
    have next := AspisR1M31Inverse.SquareProof.next_done iter stopped
    unfold AspisR1M31Inverse.field.square_n_loop
    rw [loop.eq_def]
    simp only [AspisR1M31Inverse.field.square_n_loop.body,next,bind_tc_ok]
    rfl
  | @step n before middle after cell tail ih =>
    have active : iter.start.val < iter.end.val := by omega
    obtain ⟨rest,next,inc,last,_⟩ := AspisR1M31Inverse.SquareProof.next_step iter active
    have remaining : rest.end.val-rest.start.val=n := by rw [last,inc]; omega
    obtain ⟨word,run,value,_⟩ := NFN_LPf_BaseMultiply.source before before
    have same : word=middle := UScalar.eq_of_val_eq (value.trans cell.symm)
    rw [same] at run
    unfold AspisR1M31Inverse.field.square_n_loop
    rw [loop.eq_def]
    simp only [AspisR1M31Inverse.field.square_n_loop.body,next,run,bind_tc_ok]
    exact ih rest remaining

/-- Exact raw scalar Result for the SAME native loop trace, including count0. -/
theorem native_result (count : Usize) (before after : U32)
    (trace : Trace count.val before after) :
    AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul before count =
      ok after := by
  apply loop_result trace {start:=0#usize,«end»:=count}
  simp only [UScalar.ofNatCore_val_eq,Nat.sub_zero]

#print axioms loop_result
#print axioms native_result
end NFN_NBG_SquareTrace
-- END copied NBG_SquareTrace
-- BEGIN copied NEB_SquareDomains: evidence/slice-q-compose-20261029/NEB_SquareDomains.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NEB_SquareDomains
open Aeneas Aeneas.Std Result AspisR1

theorem preserve {n : Nat} {before after : U32}
    (trace : NFN_NBG_SquareTrace.Trace n before after) (canonical : before.val<2147483647) :
    after.val<2147483647 := by
  induction trace with
  | done value => exact canonical
  | @step n before middle after cell tail ih =>
    have cm : middle.val<2147483647 := by rw [cell];exact Nat.mod_lt _ (by decide)
    exact ih cm

theorem positive {n : Nat} {before after : U32}
    (trace : NFN_NBG_SquareTrace.Trace n before after) (nonempty : 0<n) :
    after.val<2147483647 := by
  cases trace with
  | done value => omega
  | step cell tail =>
    apply preserve tail
    rw [cell]
    exact Nat.mod_lt _ (by decide)

theorem trace_exists (n : Nat) (before : U32) :
    ∃ after, NFN_NBG_SquareTrace.Trace n before after := by
  induction n generalizing before with
  | zero => exact ⟨before,.done before⟩
  | succ n ih =>
    obtain ⟨middle,run,value,_⟩ := NFN_LPf_BaseMultiply.source before before
    obtain ⟨after,tail⟩ := ih middle
    exact ⟨after,.step value tail⟩

/-- All raw initial words are allowed. Canonicality is derived after a positive
number of iterations, never imposed on the zero-iteration return. -/
theorem source (before : U32) (count : Usize) :
    ∃ after, AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul before count=ok after ∧
      NFN_NBG_SquareTrace.Trace count.val before after ∧
      (0<count.val → after.val<2147483647) := by
  obtain ⟨after,trace⟩ := trace_exists count.val before
  exact ⟨after,NFN_NBG_SquareTrace.native_result count before after trace,trace,positive trace⟩

#print axioms preserve
#print axioms positive
#print axioms trace_exists
#print axioms source
end NFN_NEB_SquareDomains
end
-- END copied NEB_SquareDomains
-- BEGIN copied NEB_InverseCalls: evidence/slice-q-compose-20261029/NEB_InverseCalls.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NEB_InverseCalls
open Aeneas Aeneas.Std Result AspisR1

/-- The actual seventeen-call DAG; no canonical input assumption or inner
callee domain/interpretation hypothesis is added. Zero is handled separately. -/
theorem nonzero (x : U32) (nonzero : x != 0#u32) :
    ∃ m t2 m1 t4 m2 t8 m3 t16 m4 t24 m5 t28 m6 t29 t30 m7 out : U32,
      FIo_Native.aspis_core.field.M31.mul x x=ok m ∧ m.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m x=ok t2 ∧ t2.val<2147483647 ∧
      AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul t2 2#usize=ok m1 ∧ m1.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m1 t2=ok t4 ∧ t4.val<2147483647 ∧
      AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul t4 4#usize=ok m2 ∧ m2.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m2 t4=ok t8 ∧ t8.val<2147483647 ∧
      AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul t8 8#usize=ok m3 ∧ m3.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m3 t8=ok t16 ∧ t16.val<2147483647 ∧
      AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul t16 8#usize=ok m4 ∧ m4.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m4 t8=ok t24 ∧ t24.val<2147483647 ∧
      AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul t24 4#usize=ok m5 ∧ m5.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m5 t4=ok t28 ∧ t28.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul t28 t28=ok m6 ∧ m6.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m6 x=ok t29 ∧ t29.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul t29 t29=ok t30 ∧ t30.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul t30 t30=ok m7 ∧ m7.val<2147483647 ∧
      FIo_Native.aspis_core.field.M31.mul m7 x=ok out ∧ out.val<2147483647 ∧
      AspisR1M31Inverse.field.M31.inv FIo_Native.aspis_core.field.M31.mul x=ok out := by
  obtain ⟨m,h_m,_,c_m⟩ := NFN_LPf_BaseMultiply.source x x
  obtain ⟨t2,h_t2,_,c_t2⟩ := NFN_LPf_BaseMultiply.source m x
  obtain ⟨m1,h_m1,_,c_m10⟩ := NFN_NEB_SquareDomains.source t2 2#usize
  have c_m1 : m1.val<2147483647 := c_m10 (by decide)
  obtain ⟨t4,h_t4,_,c_t4⟩ := NFN_LPf_BaseMultiply.source m1 t2
  obtain ⟨m2,h_m2,_,c_m20⟩ := NFN_NEB_SquareDomains.source t4 4#usize
  have c_m2 : m2.val<2147483647 := c_m20 (by decide)
  obtain ⟨t8,h_t8,_,c_t8⟩ := NFN_LPf_BaseMultiply.source m2 t4
  obtain ⟨m3,h_m3,_,c_m30⟩ := NFN_NEB_SquareDomains.source t8 8#usize
  have c_m3 : m3.val<2147483647 := c_m30 (by decide)
  obtain ⟨t16,h_t16,_,c_t16⟩ := NFN_LPf_BaseMultiply.source m3 t8
  obtain ⟨m4,h_m4,_,c_m40⟩ := NFN_NEB_SquareDomains.source t16 8#usize
  have c_m4 : m4.val<2147483647 := c_m40 (by decide)
  obtain ⟨t24,h_t24,_,c_t24⟩ := NFN_LPf_BaseMultiply.source m4 t8
  obtain ⟨m5,h_m5,_,c_m50⟩ := NFN_NEB_SquareDomains.source t24 4#usize
  have c_m5 : m5.val<2147483647 := c_m50 (by decide)
  obtain ⟨t28,h_t28,_,c_t28⟩ := NFN_LPf_BaseMultiply.source m5 t4
  obtain ⟨m6,h_m6,_,c_m6⟩ := NFN_LPf_BaseMultiply.source t28 t28
  obtain ⟨t29,h_t29,_,c_t29⟩ := NFN_LPf_BaseMultiply.source m6 x
  obtain ⟨t30,h_t30,_,c_t30⟩ := NFN_LPf_BaseMultiply.source t29 t29
  obtain ⟨m7,h_m7,_,c_m7⟩ := NFN_LPf_BaseMultiply.source t30 t30
  obtain ⟨out,h_out,_,c_out⟩ := NFN_LPf_BaseMultiply.source m7 x
  refine ⟨m,t2,m1,t4,m2,t8,m3,t16,m4,t24,m5,t28,m6,t29,t30,m7,out,h_m,c_m,h_t2,c_t2,h_m1,c_m1,h_t4,c_t4,h_m2,c_m2,h_t8,c_t8,h_m3,c_m3,h_t16,c_t16,h_m4,c_m4,h_t24,c_t24,h_m5,c_m5,h_t28,c_t28,h_m6,c_m6,h_t29,c_t29,h_t30,c_t30,h_m7,c_m7,h_out,c_out,?_⟩
  simp only [AspisR1M31Inverse.field.M31.inv,nonzero,bind_tc_ok,
    h_m,h_t2,h_m1,h_t4,h_m2,h_t8,h_m3,h_t16,h_m4,h_t24,h_m5,h_t28,h_m6,h_t29,h_t30,h_m7,h_out]
  simp [massert]

theorem zero : AspisR1M31Inverse.field.M31.inv FIo_Native.aspis_core.field.M31.mul 0#u32 =
    Port4C_InverseExecution.inverse_owned 0#u32 := NFN_NBG_InverseBridge.inverse_result _

#print axioms nonzero
#print axioms zero
end NFN_NEB_InverseCalls
end
-- END copied NEB_InverseCalls
-- BEGIN copied NEO_TailReference: evidence/slice-q-compose2-20261102/NEO_TailReference.lean
set_option autoImplicit false
namespace NFN_NEO_TailReference
open Aeneas Aeneas.Std Result AspisR1

def inverseOps : NEO_TailRef.InverseOps Unit where
 mul := FIo_Native.aspis_core.field.M31.mul
 square := AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul

/-- Exact independently extracted addition chain, including the zero panic. -/
theorem inverse (x : U32) :
 NEO_TailRef.inverse inverseOps x =
 AspisR1M31Inverse.field.M31.inv FIo_Native.aspis_core.field.M31.mul x := rfl

/-- Exact independently extracted native opening range; arithmetic is release
wrapping in both definitions and bounds are proved by the existing caller. -/
theorem opening (proof : Slice U8) (i : Usize) :
 NEO_TailRef.opening proof i=Port4B_Opening.opening proof i := rfl

/-- The constructor Result is checked; no unchecked FibreIndex alias is used
as a constructor implementation. Mapping the one rejected value stays explicit. -/
theorem checked {C : Type} (error : C) (u : Usize) :
 NFN_NEB_GeometryIndices.indexPort error u =
 (do let r ← NEO_TailRef.checked u
     ok (match r with | .Ok x => .Ok x | .Err _ => .Err error)) := by
 unfold NFN_NEB_GeometryIndices.indexPort
 rw [NEA_Index.all_inputs]
 unfold NEO_TailRef.checked
 split <;> simp_all [bind_tc_ok]

#print axioms inverse
#print axioms opening
#print axioms checked
end NFN_NEO_TailReference
-- END copied NEO_TailReference
-- BEGIN copied NEO_InverseLog: evidence/slice-q-compose2-20261102/NEO_InverseLog.lean
set_option autoImplicit false
namespace NFN_NEO_InverseLog
open Aeneas Aeneas.Std Result AspisR1
inductive Call where
 | product (left right reply : U32)
 | square (input : U32) (count : Usize) (reply : U32)

def legal : Call → Prop
 | .product a b r => FIo_Native.aspis_core.field.M31.mul a b=ok r ∧ r.val<2147483647
 | .square a n r => AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul a n=ok r ∧ r.val<2147483647

def chain (x m t2 m1 t4 m2 t8 m3 t16 m4 t24 m5 t28 m6 t29 t30 m7 out : U32) : List Call :=
 [.product x x m,.product m x t2,.square t2 2#usize m1,.product m1 t2 t4,
  .square t4 4#usize m2,.product m2 t4 t8,.square t8 8#usize m3,.product m3 t8 t16,
  .square t16 8#usize m4,.product m4 t8 t24,.square t24 4#usize m5,.product m5 t4 t28,
  .product t28 t28 m6,.product m6 x t29,.product t29 t29 t30,
  .product t30 t30 m7,.product m7 x out]

theorem nonzero (x : U32) (nonzero : x != 0#u32) :
 ∃ m t2 m1 t4 m2 t8 m3 t16 m4 t24 m5 t28 m6 t29 t30 m7 out : U32,
 let calls := chain x m t2 m1 t4 m2 t8 m3 t16 m4 t24 m5 t28 m6 t29 t30 m7 out
 calls.length=17 ∧ (∀ call∈calls,legal call) ∧
 NEO_TailRef.inverse NFN_NEO_TailReference.inverseOps x=ok out ∧ out.val<2147483647 := by
 obtain ⟨m,t2,m1,t4,m2,t8,m3,t16,m4,t24,m5,t28,m6,t29,t30,m7,out,
 hm,cm,ht2,ct2,hm1,cm1,ht4,ct4,hm2,cm2,ht8,ct8,hm3,cm3,ht16,ct16,
 hm4,cm4,ht24,ct24,hm5,cm5,ht28,ct28,hm6,cm6,ht29,ct29,ht30,ct30,hm7,cm7,hout,cout,run⟩ :=
 NFN_NEB_InverseCalls.nonzero x nonzero
 refine ⟨m,t2,m1,t4,m2,t8,m3,t16,m4,t24,m5,t28,m6,t29,t30,m7,out,?_,?_,?_,cout⟩
 · rfl
 · intro call member
   simp only [chain,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
   all_goals simp_all [legal]
 · rw [NFN_NEO_TailReference.inverse]
   exact run

theorem zero : NEO_TailRef.inverse NFN_NEO_TailReference.inverseOps 0#u32=fail .assertionFailure := by
 simp [NEO_TailRef.inverse,massert]

#print axioms nonzero
#print axioms zero
end NFN_NEO_InverseLog
-- END copied NEO_InverseLog
-- BEGIN copied NEW_InverseComplete: evidence/slice-q-compose4-20261104/NEW_InverseComplete.lean
set_option autoImplicit false
namespace NFN_NEW_InverseComplete
open Aeneas Aeneas.Std Result AspisR1

/-- Actual-body extraction identifies the full independent reference, including rejection. -/
theorem reference (x : U32) : NEW_InverseActual.aspis_core.field.M31.inv x =
    NEO_TailRef.inverse NFN_NEO_TailReference.inverseOps x :=
  (NFN_NEW_InverseAssociation.emitted x).trans (NFN_NEO_TailReference.inverse x).symm

/-- Entire Result/state/semantic-effects lift on the same model state.
The runtime's panic interpretation is retained; no empty native panic-I/O claim. -/
theorem result_state_effects {S Event : Type} (state : S) (x : U32) :
    NEB_PureFrame.run (Event:=Event) state (NEW_InverseActual.aspis_core.field.M31.inv x) =
      NEB_PureFrame.run (Event:=Event) state (Port4C_InverseExecution.inverse_owned x) := by
  rw [NFN_NEW_InverseAssociation.cohort]

/-- Reuse the already proved legal DAG. The returned word is now tied to the
ACTUAL frozen extraction, rather than only to the earlier logged clone. -/
theorem nonzero_calls (x : U32) (nonzero : x != 0#u32) :
 ∃ m t2 m1 t4 m2 t8 m3 t16 m4 t24 m5 t28 m6 t29 t30 m7 out : U32,
 let calls := NFN_NEO_InverseLog.chain x m t2 m1 t4 m2 t8 m3 t16 m4 t24 m5 t28 m6 t29 t30 m7 out
 calls.length=17 ∧ (∀ call∈calls,NFN_NEO_InverseLog.legal call) ∧
 NEW_InverseActual.aspis_core.field.M31.inv x=ok out ∧ out.val<2147483647 := by
 obtain ⟨m,t2,m1,t4,m2,t8,m3,t16,m4,t24,m5,t28,m6,t29,t30,m7,out,count,legal,run,canonical⟩ :=
   NFN_NEO_InverseLog.nonzero x nonzero
 exact ⟨m,t2,m1,t4,m2,t8,m3,t16,m4,t24,m5,t28,m6,t29,t30,m7,out,count,legal,
   (reference x).trans run,canonical⟩

#print axioms reference
#print axioms result_state_effects
#print axioms nonzero_calls
end NFN_NEW_InverseComplete
-- END copied NEW_InverseComplete
-- BEGIN copied NBS_GeometryDomains: lean/NBS_GeometryDomains.lean
set_option autoImplicit false
namespace NFN_NBS_GeometryDomains
open Aeneas Aeneas.Std AspisR1
/-- All real geometry sizes, including empty ranges; no allocation success
or result vector is assumed. TX2 uses start10/end22. -/
theorem sizes (start stop : Nat) (order : start≤stop) (hi : stop≤22) :
    stop-start≤22 ∧ (stop-start)*5≤110 ∧
    (start=10 → stop-start≤12 ∧ (stop-start)*5≤60) := by omega

theorem aligned (u : Nat) (bound : u<262144) :
    u/4*4<262144 ∧ u/4*4+3<262144 ∧
    u/4*4≤u ∧ u≤u/4*4+3 := by omega

/-- A selected record is exactly five consecutive entries in the SAME flat
vector. This also proves the allocation/index arithmetic does not overflow. -/
theorem group (n i j : Nat) (hn : n≤22) (hi : i<n) (hj : j<5) :
    5*i+j<5*n ∧ 5*i+j<110 ∧ 5*i+j<18446744073709551616 := by omega

theorem accessor (start count index : Nat) (lo : start ≤ index) (hi : index<start+count) :
    index-start<count ∧ start+(index-start)=index := by omega

/-- Accepted zero checks and canonicality imply nonzero natural residues,
so a successful native path never inverts field zero. -/
theorem nonzero (word : Nat) (canonical : word<2147483647) (guard : word≠0) :
    word%2147483647≠0 := by rw [Nat.mod_eq_of_lt canonical];exact guard

#print axioms sizes
#print axioms aligned
#print axioms group
#print axioms accessor
#print axioms nonzero
#print axioms AspisR1.Port4C_PrefixMeaning.total
#print axioms AspisR1.Port4C_BatchInverse.backward_exact
end NFN_NBS_GeometryDomains
-- END copied NBS_GeometryDomains
-- BEGIN copied NET_GeometryAllocation: evidence/slice-q-compose3-20261102/NET_GeometryAllocation.lean
set_option autoImplicit false
namespace NFN_NET_GeometryAllocation

/-- Frame observations at every offset compose a single extend operation.
This is a value law; native allocation and live-place transport are separate. -/
theorem extend_from_windows {T : Type} (before after values : List T)
    (length : after.length = before.length + values.length)
    (windows : ∀ (offset : Nat) (valid : offset < after.length),
      after[offset] = if h : offset < before.length then before[offset]
      else values[offset-before.length]'(by omega)) :
    after = before ++ values := by
  apply List.ext_getElem
  · simp only [List.length_append]; exact length
  · intro offset ha hb
    rw [windows offset ha]
    by_cases inside : offset < before.length
    · simp only [dif_pos inside,List.getElem_append_left inside]
    · simp only [dif_neg inside,List.getElem_append_right (by omega : before.length ≤ offset)]

/-- Both native buffers keep their nongrowing capacity on one five-word
append and one line-word push, at the same query cursor. -/
theorem forward_invariant (count cursor flatLength lineLength : Nat)
    (bound : count ≤ 22) (active : cursor < count)
    (flat : flatLength = 5 * cursor) (line : lineLength = cursor) :
    flatLength + 5 = 5 * (cursor+1) ∧ lineLength+1 = cursor+1 ∧
    flatLength+5 ≤ 5*count ∧ lineLength+1 ≤ count ∧
    flatLength+5 ≤ 110 := by omega

/-- Exact reverse traversal bounds, including the first and final cells. -/
theorem reverse_invariant (count remaining : Nat)
    (bound : count ≤ 22) (positive : 0 < remaining) (inside : remaining ≤ 5*count) :
    remaining-1 < 5*count ∧ remaining-1 < 110 ∧
    remaining-1+1 = remaining ∧ remaining-1 < remaining := by omega

/-- A single indexed write preserves every distinct live value window. -/
theorem backward_frame {T : Type} (before : List T) (index offset : Nat) (value : T)
    (different : offset ≠ index) :
    (before.set index value)[offset]? = before[offset]? := by
  exact List.getElem?_set_ne different.symm

#print axioms extend_from_windows
#print axioms forward_invariant
#print axioms reverse_invariant
#print axioms backward_frame
end NFN_NET_GeometryAllocation
-- END copied NET_GeometryAllocation
-- BEGIN copied NEW_GeometryReverse: evidence/slice-q-compose4-20261104/NEW_GeometryReverse.lean
set_option autoImplicit false
namespace NFN_NEW_GeometryReverse
open Aeneas.Std
open AspisR1
open S7Kani2PrefixLoop (wordMul)
open Port4C_BatchInverse (cell)

/-- Pointwise native write observations identify the SAME output list, including
all unmodified cells. No independently selected whole-output equality is assumed. -/
theorem write_from_windows (before after : List U32) (index : Nat) (value : U32)
    (active : index < before.length) (size : after.length = before.length)
    (windows : ∀ j, j < before.length →
      after[j]? = if j = index then some value else before[j]?) :
    after = before.set index value := by
  apply List.ext_getElem?
  intro j
  by_cases h : j < before.length
  · rw [windows j h]
    by_cases same : j = index
    · subst j
      simp only [ite_true,List.getElem?_set_self active]
    · simp only [same,if_false,List.getElem?_set_ne (Ne.symm same)]
  · have ha : after.length ≤ j := by omega
    have hb : (before.set index value).length ≤ j := by simpa only [List.length_set] using (show before.length ≤ j by omega)
    rw [List.getElem?_eq_none ha,List.getElem?_eq_none hb]

/-- One step uses two ordered products. Their replies have already been
instantiated by the existing emitted multiplication law; no arithmetic Kani. -/
inductive Trace (flat prefixes : List U32) :
    Nat → List U32 → U32 → List U32 → U32 → List (U32 × U32) → Prop
 | done (inverse : List U32) (suffix : U32) :
     Trace flat prefixes 0 inverse suffix inverse suffix []
 | step (n : Nat) (inverse next final : List U32) (suffix finalSuffix : U32)
     (tailCalls : List (U32 × U32))
     (active : n < inverse.length)
     (size : next.length = inverse.length)
     (windows : ∀ j, j < inverse.length → next[j]? =
       if j = n then some (wordMul suffix (cell prefixes n)) else inverse[j]?)
     (tail : Trace flat prefixes n next (wordMul suffix (cell flat n)) final finalSuffix tailCalls) :
     Trace flat prefixes (n+1) inverse suffix final finalSuffix
       ((suffix,cell prefixes n)::(suffix,cell flat n)::tailCalls)

def suffixAfter (flat : List U32) : Nat → U32 → U32
 | 0,suffix => suffix
 | n+1,suffix => suffixAfter flat n (wordMul suffix (cell flat n))

/-- The exact mutable output AND returned suffix compose by reverse induction.
This consumes every frame observation, not just the newly written cell. -/
theorem state (flat prefixes : List U32) {n : Nat} {inverse final : List U32}
    {suffix finalSuffix : U32} {calls : List (U32 × U32)}
    (trace : Trace flat prefixes n inverse suffix final finalSuffix calls) :
    final = Port4C_OwnedInverse.model flat prefixes n inverse suffix ∧
      finalSuffix = suffixAfter flat n suffix := by
  induction trace with
  | done => exact ⟨rfl,rfl⟩
  | step n inverse next final suffix finalSuffix calls active size windows tail ih =>
    have same := write_from_windows inverse next n (wordMul suffix (cell prefixes n)) active size windows
    rcases ih with ⟨output,returned⟩
    constructor
    · rw [output,same]
      rfl
    · exact returned

/-- The two calls in each native cell precede all calls for lower cells. -/
theorem call_count (flat prefixes : List U32) {n : Nat} {inverse final : List U32}
    {suffix finalSuffix : U32} {calls : List (U32 × U32)}
    (trace : Trace flat prefixes n inverse suffix final finalSuffix calls) :
    calls.length = 2*n := by
  induction trace with
  | done => rfl
  | step n inverse next final suffix finalSuffix calls active size windows tail ih =>
    simp only [List.length_cons]
    omega

/-- Deterministic ordered effects, including BOTH products before the next cell. -/
def callLog (flat prefixes : List U32) : Nat → U32 → List (U32 × U32)
 | 0,_ => []
 | n+1,suffix => (suffix,cell prefixes n)::(suffix,cell flat n)::
     callLog flat prefixes n (wordMul suffix (cell flat n))

theorem ordered_calls (flat prefixes : List U32) {n : Nat} {inverse final : List U32}
    {suffix finalSuffix : U32} {calls : List (U32 × U32)}
    (trace : Trace flat prefixes n inverse suffix final finalSuffix calls) :
    calls = callLog flat prefixes n suffix := by
  induction trace with
  | done => rfl
  | step n inverse next final suffix finalSuffix calls active size windows tail ih =>
    simp only [callLog,ih]

#print axioms write_from_windows
#print axioms state
#print axioms call_count
#print axioms ordered_calls
end NFN_NEW_GeometryReverse
-- END copied NEW_GeometryReverse
-- BEGIN copied NFB_ZeroScan: evidence/slice-q-compose5-20261104/NFB_ZeroScan.lean
set_option autoImplicit false
namespace NFN_NFB_ZeroScan
open Aeneas Aeneas.Std Result ControlFlow AspisR1

def zeroStep (state : core.slice.iter.Iter U32 × Unit) :
    Result (ControlFlow (core.slice.iter.Iter U32 × Unit) (Bool × core.slice.iter.Iter U32)) := do
  let (next,it) ← core.slice.iter.IteratorSliceIter.next state.1
  match next with
  | none => ok (done (false,it))
  | some value =>
    if decide (value=0#u32) then ok (done (true,it)) else ok (cont (it,()))

/-- The actual emitted zero callback has no arithmetic/domain/effect premise. -/
theorem zero_callback (x : U32) :
    NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut () x =
      ok (decide (x=0#u32),()) := by
  simp only [NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool.call_mut,
    NEW_GeometryActual.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq,
    NEW_GeometryActual.aspis_core.field.M31.ZERO,bind_tc_ok]

/-- One native iterator/callback observation is associated with this exact
cohort loop body. The primitive is the SAME slice iterator, not a free reply. -/
theorem zero_body (state : core.slice.iter.Iter U32 × Unit) :
    Port3_BatchStd.anyBody (core.iter.traits.iterator.IteratorSliceIter U32)
      NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool
      state = zeroStep state := by
  rcases state with ⟨it,u⟩
  cases u
  simp only [Port3_BatchStd.anyBody,zeroStep,
    core.iter.traits.iterator.IteratorSliceIter,
    NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool,
    zero_callback,bind_tc_ok,uncurry]
  apply NFN_NEW_GeometryRawBody.bind_congr
  rintro ⟨next,after⟩
  cases next with
  | none => rfl
  | some value =>
    simp only [uncurry]

/-- Whole partial Result transport reuses the identical body in the coherent
least-fixpoint loop. This does not unfold a buffer or assume termination. -/
theorem zero_loop (it : core.slice.iter.Iter U32) :
    Port3_BatchStd.anyDefault (core.iter.traits.iterator.IteratorSliceIter U32)
      NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool it () =
      loop zeroStep (it,()) := by
  unfold Port3_BatchStd.anyDefault
  have same := funext zero_body
  rw [same]

theorem native_cursor_cover (n k : Nat) (size : n=10 ∨ n=12) (active : k<n) :
    k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 := by omega

theorem native_half_cover (n k : Nat) : k<n/2 ∨ n/2≤k := by omega

theorem zero_witness_cover (row : Fin 5 → U32) :
    (∀ j, row j≠0#u32) ∨ ∃ j, row j=0#u32 := by
  classical
  by_cases h : ∀ j, row j≠0#u32
  · exact Or.inl h
  · exact Or.inr (Classical.byContradiction (fun hn => h (fun j hz => hn ⟨j,hz⟩)))

/-- Pure iterator/callback execution carries the separate caller state intact.
Native frame observations and the pinned source establish the same separation. -/
theorem zero_loop_frame {State : Type} (it : core.slice.iter.Iter U32) (state : State) :
    (Port3_BatchStd.anyDefault (core.iter.traits.iterator.IteratorSliceIter U32)
      NEW_GeometryActual.verifier.QueryGeometry.for_range.closure_3.Insts.CoreOpsFunctionFnMutTupleSharedM31Bool it (),state) =
    (loop zeroStep (it,()),state) := by rw [zero_loop]

#print axioms zeroStep
#print axioms zero_callback
#print axioms zero_body
#print axioms zero_loop
#print axioms zero_loop_frame
#print axioms native_cursor_cover
#print axioms native_half_cover
#print axioms zero_witness_cover
#print axioms NFN_NEW_GeometryComplete.complete_raw
#print axioms NFN_NEW_GeometryComplete.complete
#print axioms NFN_NEW_GeometryComplete.result_state
#print axioms NFN_NEW_GeometryComplete.accepted
#print axioms NFN_NEW_InverseComplete.result_state_effects
#print axioms NFN_NEW_GeometryReverse.state
end NFN_NFB_ZeroScan
-- END copied NFB_ZeroScan
-- BEGIN copied NFB_ZeroFinite: evidence/slice-q-compose5-20261104/NFB_ZeroFinite.lean
set_option autoImplicit false
namespace NFN_NFB_ZeroFinite
open Aeneas Aeneas.Std Result ControlFlow

/-- Finite model retains the SAME slice and its exact native cursor; zero
short-circuit consumes the selected word and retains the untouched suffix. -/
def bounded : Nat → core.slice.iter.Iter U32 → Result (Bool × core.slice.iter.Iter U32)
 | 0,it => ok (false,it)
 | n+1,it => do
   let (next,after) ← core.slice.iter.IteratorSliceIter.next it
   match next with
   | none => ok (false,after)
   | some value => if decide (value=0#u32) then ok (true,after) else bounded n after

theorem next_active (it : core.slice.iter.Iter U32) (h : it.i < it.slice.val.length) :
    core.slice.iter.IteratorSliceIter.next it =
      ok (some it.slice.val[it.i],{it with i:=it.i+1}) := by
 unfold core.slice.iter.IteratorSliceIter.next
 split
 · rfl
 · rename_i hn; exact False.elim (hn h)

theorem next_end (it : core.slice.iter.Iter U32) (h : it.slice.val.length ≤ it.i) :
    core.slice.iter.IteratorSliceIter.next it=ok (none,it) := by
 unfold core.slice.iter.IteratorSliceIter.next
 split
 · rename_i hn
   have bad : it.i < it.slice.val.length := hn
   omega
 · rfl

/-- Induction is on remaining words, never on an unfolded concrete buffer. -/
theorem complete (it : core.slice.iter.Iter U32) (fuel : Nat)
    (remaining : it.i+fuel=it.slice.val.length) :
    loop NFN_NFB_ZeroScan.zeroStep (it,())=bounded fuel it := by
 induction fuel generalizing it with
 | zero =>
   rw [loop.eq_def]
   simp only [NFN_NFB_ZeroScan.zeroStep,next_end it (by omega),bind_tc_ok,bounded,uncurry]
 | succ fuel ih =>
   have active : it.i < it.slice.val.length := by omega
   have rest : ({it with i:=it.i+1} : core.slice.iter.Iter U32).i+fuel=it.slice.val.length := by
     simp only; omega
   rw [loop.eq_def]
   simp only [NFN_NFB_ZeroScan.zeroStep,next_active it active,bind_tc_ok,bounded,uncurry]
   by_cases hz : decide (it.slice.val[it.i] = 0#u32) = true
   · simp only [hz,if_true]
   · simpa only [hz,Bool.false_eq_true,if_false] using ih {it with i:=it.i+1} rest

#print axioms next_active
#print axioms next_end
#print axioms complete
end NFN_NFB_ZeroFinite
-- END copied NFB_ZeroFinite

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
