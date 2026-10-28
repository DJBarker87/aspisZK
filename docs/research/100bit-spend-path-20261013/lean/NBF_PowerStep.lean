import NBF_QueryStep
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBF_PowerStep
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
open Port3_PushFrame (bind_success)
def Canonical (q : NBF_RowInstall.Q) : Prop :=
 ∀ k, (S7Kani2OwnedRowRefinement.powerLimb (Port3_RowsInstall.toK q) k).val<2^31-1
/-- Exact remaining other-lane operation law. It mentions only one field call,
its canonical arguments and returned carrier, never a query/transaction result. -/
def NBC_Qm31Canonical (ops : Ops) : Prop :=
 ∀ x y z, Canonical x → Canonical y → ops.op9 x y=ok z → Canonical z

theorem accumulate (ops : Ops) (field : NBC_Qm31Canonical ops) (p : verifier.Prepared)
 (a out : verifier.Accumulator) (node : U32) (value : Stage2E)
 (b bout : verifier.BatchedWeights) (size : a.weights.val.length=64)
 (progress : S7JoinRowsTrace.Progress b.terms.val 0 (Port3_RowsInstall.toBW b))
 (hq : Canonical a.power) (rho : Canonical p.rho)
 (run : verifier.accumulate_batched_with_node (NBF_Accumulate.install ops)
   p a node value b=ok (out,bout)) : Canonical out.power := by
 obtain ⟨basis,mid,hbasis,hrows,terms,len,phase,body⟩ := NBF_Accumulate.rows
   ops p a node value b size progress hq
 rw [body] at run
 simp only [lift,bind_tc_ok] at run
 obtain ⟨product,hproduct,run⟩ := bind_success _ _ _ run
 obtain ⟨rhs,hrhs,run⟩ := bind_success _ _ _ run
 obtain ⟨marked,hmarked,run⟩ := bind_success _ _ _ run
 obtain ⟨power,hpower,run⟩ := bind_success _ _ _ run
 cases Result.ok.inj run
 exact field a.power p.rho power hq rho hpower

theorem query (ops : Ops) (field : NBC_Qm31Canonical ops) (proof : Slice U8)
 (p : verifier.Prepared) (a out : verifier.Accumulator) (g : Array Stage2E 29#usize)
 (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
 (size : a.weights.val.length=64)
 (progress : S7JoinRowsTrace.Progress b.terms.val 0 (Port3_RowsInstall.toBW b))
 (hq : Canonical a.power) (rho : Canonical p.rho)
 (run : verifier.candidate.query_values (NBF_Accumulate.install ops)
   proof p a g none geometry b=ok (.Ok (out,bout))) : Canonical out.power := by
 obtain ⟨query,opening,dots,inverse,circle,values,line,node,
   hquery,hopening,hdots,hinverse,hcircle,hline,haccum⟩ :=
   NBF_QueryCuts.accepted (NBF_Accumulate.install ops) proof p a out g none geometry b bout run
 exact accumulate ops field p a out node line b bout size progress hq rho haccum
#print axioms accumulate
#print axioms query
end NBF_PowerStep
