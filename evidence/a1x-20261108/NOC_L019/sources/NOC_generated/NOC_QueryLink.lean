import NOC_ReadTransport
import NNX_CurrentQuery
import NNX_QueryOutput
import NNX_C1Gather
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOC_QueryLink
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody

/-- Library (LIBC_QueryOps.ops) and installed model query dictionaries. -/
abbrev Dsel := NFS_QueryOps.installed (NFS_CallerDomains.select LIBC_QueryOps.seed)
abbrev Dcon := NFS_QueryOps.installed NJJ_QueryOps.concrete
abbrev inst (D : Ops) :=
 verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact D

theorem op21_sel : Dsel.op21 = NFS_ReadCanonical.read := rfl
theorem op21_con : Dcon.op21 = SAQ_Decoder.read := rfl

/-- The opening-value closure agrees on every reached index i < 4. -/
theorem call_eq (c : verifier.candidate.query_values.closure) (i : Usize) (hi : i.val < 4) :
 (inst Dsel).call_mut c i = (inst Dcon).call_mut c i := by
 simp only [inst,verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact,
  verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut,
  op21_sel,op21_con,NOC_ReadTransport.read _ i hi]

theorem loop_eq (l : List Usize) (h : ∀ i ∈ l, i.val < 4) (c : verifier.candidate.query_values.closure) :
 OraclePortStdBuilder.fromFnLoop (inst Dsel) l c = OraclePortStdBuilder.fromFnLoop (inst Dcon) l c := by
 induction l generalizing c with
 | nil => rfl
 | cons i is ih =>
  have head : verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut Dsel c i = verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact.call_mut Dcon c i := call_eq c i (h i (by simp))
  have tail : ∀ c', OraclePortStdBuilder.fromFnLoop (inst Dsel) is c' =
    OraclePortStdBuilder.fromFnLoop (inst Dcon) is c' :=
   fun c' => ih (fun j hj => h j (by simp [hj])) c'
  simp only [OraclePortStdBuilder.fromFnLoop,head,tail]

theorem closure_eq (q : verifier.candidate.query_values.closure) :
 Dsel.op0 4#usize (inst Dsel) q = Dcon.op0 4#usize (inst Dcon) q := by
 show OraclePortStdBuilder.fromFn 4#usize (inst Dsel) q = OraclePortStdBuilder.fromFn 4#usize (inst Dcon) q
 unfold OraclePortStdBuilder.fromFn
 rw [loop_eq (OraclePortStdBuilder.indices 4#usize)
  (fun i hi => by have := NNX_C1Gather.member 4#usize i hi; scalar_tac) q]

/-- One query iteration: the two dictionaries differ only in op21. -/
theorem values_eq (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (geo : verifier.QueryGeometry)
 (b : verifier.BatchedWeights) :
 verifier.candidate.query_values Dsel proof p a g none geo b =
 verifier.candidate.query_values Dcon proof p a g none geo b := by
 unfold verifier.candidate.query_values
 simp only [closure_eq]
 rfl

/-- The whole tx1 query loop, on the SAME canonical prestate. -/
theorem loop (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (geo : verifier.QueryGeometry)
 (b : verifier.BatchedWeights)
 (canonical : NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g))
 (domain : NFS_QueryInvariant.Domain p 0 10 a b) (start : a.next.val = 0) :
 verifier.candidate.query_loop Dcon proof p a g none geo b 10#usize =
 verifier.candidate.query_loop Dsel proof p a g none geo b 10#usize := by
 rw [← NFS_QueryLoopRoot.tx1 NJJ_QueryOps.concrete proof p a g geo b 0 0 canonical domain start,
  ← NFS_QueryLoopRoot.tx1 (NFS_CallerDomains.select LIBC_QueryOps.seed) proof p a g geo b 0 0 canonical domain start,
  NFS_QueryLoopRoot.finite NJJ_QueryOps.concrete proof p g geo 0 0 0 10#usize (by decide) canonical 10 (.Ok (a,b)) domain,
  NFS_QueryLoopRoot.finite (NFS_CallerDomains.select LIBC_QueryOps.seed) proof p g geo 0 0 0 10#usize (by decide) canonical 10 (.Ok (a,b)) domain]
 congr 1
 funext a' b'
 exact (values_eq proof p a' g geo b').symm

/-- X2 link: returned LIBC_QueryLoop value on its Domain is the installed
model query loop's full Result, at the SAME native carriers. -/
theorem link (a : LIBC_QueryLoop.Args) (env : RSL.Env) (d : LIBC_QueryLoop.Domain a)
 (after : LIB_VCarriers.Acc) (pending : LIB_VCarriers.Weights)
 (called : LIBC_QueryLoop.value a env = .ok (after,pending)) :
 verifier.candidate.query_loop NNH_Run5bQuerySlots.model (LIBC_Bytes.raw a.1) (LIBC_QueryLoop.nativeP a)
  (LIBC_QueryLoop.nativeA a) (LIBC_QueryLoop.nativeG a) none (LIBC_QueryLoop.geo a)
  (LIBC_QueryLoop.pending a) 10#usize = .ok (.Ok (LIBC_VStateCarriers.toAcc after,pending)) := by
 have run := NNX_QueryOutput.source a env after pending called
 exact (loop _ _ _ _ _ _ d.2.2.gCanonical d.2.2.invariant d.2.1).trans
  ((NFS_QueryLoopRoot.tx1 (NFS_CallerDomains.select LIBC_QueryOps.seed) (LIBC_Bytes.raw a.1)
   (LIBC_QueryLoop.nativeP a) (LIBC_QueryLoop.nativeA a) (LIBC_QueryLoop.nativeG a) (LIBC_QueryLoop.geo a)
   (LIBC_QueryLoop.pending a) 0 0 d.2.2.gCanonical d.2.2.invariant d.2.1).symm.trans run)

/-- The same at the installed current-dictionary query leaves. -/
theorem current (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env0 : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (a : LIBC_QueryLoop.Args) (env : RSL.Env) (d : LIBC_QueryLoop.Domain a)
 (after : LIB_VCarriers.Acc) (pending : LIB_VCarriers.Weights)
 (called : LIBC_QueryLoop.value a env = .ok (after,pending)) :
 verifier.candidate.query_loop (NNX_CurrentQuery.actual m env0 err r) (LIBC_Bytes.raw a.1) (LIBC_QueryLoop.nativeP a)
  (LIBC_QueryLoop.nativeA a) (LIBC_QueryLoop.nativeG a) none (LIBC_QueryLoop.geo a)
  (LIBC_QueryLoop.pending a) 10#usize = .ok (.Ok (LIBC_VStateCarriers.toAcc after,pending)) :=
 (NNX_CurrentQuery.source m env0 err r _ _ _ _ _ _ d.2.2.invariant d.2.1).trans
  (link a env d after pending called)
#print axioms call_eq
#print axioms loop_eq
#print axioms closure_eq
#print axioms values_eq
#print axioms loop
#print axioms link
#print axioms current
end AspisR1.NOC_QueryLink
end
