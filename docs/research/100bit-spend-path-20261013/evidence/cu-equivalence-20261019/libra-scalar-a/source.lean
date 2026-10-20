import CuSavingsLibraSourcePowers
import CuSavingsLibraSourcePerm
import OccupancyRangeTraversal
set_option autoImplicit false
namespace AspisR1.CuSavingsLibraSourceScalar
open Aeneas Aeneas.Std Result ControlFlow AspisR1Libra
open CuSavingsLibraSourceModel CuSavingsLibraSourceControl
open OccupancyRangeTraversal
variable {R S : Type} [CommSemiring R] [CommSemiring S] [Shared]
variable (A : Arithmetic R S)

abbrev Powers := Array K 4#usize
abbrev Points := Array E 4#usize
abbrev Closure := Points × Powers
abbrev State := Range × E × Closure

def prefix (f : Nat → R) (n : Nat) : R := ((List.range n).map f).sum

theorem prefix_succ (f : Nat → R) (n : Nat) : prefix f (n+1)=prefix f n+f n := by
  simp only [prefix,List.range_succ,List.map_append,List.sum_append,List.map_singleton,List.sum_singleton]

def body (state : State) : Result (ControlFlow State E) := do
  let (iter,acc,c) := state
  let (entry,iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match entry with
  | none => .ok (.done acc)
  | some i =>
    let (acc1,c1) ← Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut c (acc,i)
    .ok (.cont (iter1,acc1,c1))

theorem fold_source (f : Powers) (p : Points) :
    Weights.scalar_factor f p = (do
      let value ← execute body ({start:=0#usize,«end»:=4#usize},field.wide_exact.WideExact.ZERO,(p,f))
      field.wide_exact.WideExact.mul_m31 value QUARTER) := rfl

def term (f : Powers) (p : Points) (i : Nat) : R :=
  A.decodeE (lookup p field.wide_exact.WideExact.ZERO (CuSavingsLibraSourcePerm.perm i)) *
    A.embedding (A.decodeK (lookup f field.QM31.ONE i))

theorem source_success (f : Powers) (p : Points)
    (hf : ∀ i, i<4 → A.canonicalK (lookup f field.QM31.ONE i))
    (hp : ∀ i, i<4 → A.canonicalE (lookup p field.wide_exact.WideExact.ZERO i)) :
    ∃ value, Weights.scalar_factor f p=.ok value ∧ A.canonicalE value ∧
      A.decodeE value=prefix (term A f p) 4*A.quarter := by
  let I : State → Prop := fun state =>
    state.1.end=4#usize ∧ state.1.start.val≤4 ∧ state.2.2=(p,f) ∧
    A.canonicalE state.2.1 ∧ A.decodeE state.2.1=prefix (term A f p) state.1.start.val
  let Q : E → Prop := fun value => A.canonicalE value ∧ A.decodeE value=prefix (term A f p) 4
  have step : ∀ state, I state → state.1.start.val<4 →
      ∃ next, body state=.ok (.cont next) ∧ I next ∧ next.1.start.val=state.1.start.val+1 := by
    intro state hs hi
    rcases state with ⟨iter,acc,c⟩
    rcases hs with ⟨hend,hstart,hc,hacc,hvalue⟩
    change c=(p,f) at hc
    subst c
    have hit : iter.start.val<iter.end.val := by rw [hend];simpa using hi
    obtain ⟨iter1,hnext,hiter1,hend1,_⟩ := next_step iter hit
    obtain ⟨index,hindex,hib,hiv⟩ := CuSavingsLibraSourcePerm.source iter.start hi
    have hpr := read p field.wide_exact.WideExact.ZERO index (by scalar_tac)
    have hfr := read f field.QM31.ONE iter.start (by scalar_tac)
    obtain ⟨product,hproduct,hproductC,hproductV⟩ := A.mixed
      (lookup p field.wide_exact.WideExact.ZERO index.val)
      (lookup f field.QM31.ONE iter.start.val) (hp index.val hib) (hf iter.start.val hi)
    obtain ⟨sum,hsum,hsumC,hsumV⟩ := A.add acc product hacc hproductC
    refine ⟨(iter1,sum,(p,f)),?_,?_,hiter1⟩
    · unfold body Weights.scalar_factor.closure.Insts.CoreOpsFunctionFnMutPairWideExactUsizeWideExact.call_mut
      simp only [hnext,bind_tc_ok]
      change (do
        let index ← Array.index_usize PERM iter.start
        let point ← Array.index_usize p index
        let scalar ← Array.index_usize f iter.start
        let product ← field.wide_exact.WideExact.mul_qm31 point scalar
        let sum ← field.wide_exact.WideExact.add acc product
        .ok (.cont (iter1,sum,(p,f)))) = _
      rw [hindex,hpr,hfr,hproduct,hsum]
      rfl
    · refine ⟨hend1.trans hend,by omega,rfl,hsumC,?_⟩
      change A.decodeE sum=prefix (term A f p) iter1.start.val
      rw [hiter1,prefix_succ,hsumV,hvalue,hproductV,hiv]
      rfl
  have done : ∀ state, I state → state.1.start.val=4 →
      ∃ value, body state=.ok (.done value) ∧ Q value := by
    intro state hs hi
    rcases state with ⟨iter,acc,c⟩
    rcases hs with ⟨hend,_,_,hacc,hvalue⟩
    have hd := next_done iter (by rw [hend];simpa using (show iter.start.val≥4 by omega))
    refine ⟨acc,?_,hacc,?_⟩
    · unfold body
      simpa only [hd,bind_tc_ok]
    · simpa only [hi] using hvalue
  have initial : I ({start:=0#usize,«end»:=4#usize},field.wide_exact.WideExact.ZERO,(p,f)) :=
    ⟨rfl,by scalar_tac,rfl,A.zero,by simpa only [prefix,List.range_zero,List.map_nil,List.sum_nil] using A.zero_value⟩
  obtain ⟨sum,hloop,hsumC,hsumV⟩ := execute_invariant body (fun state : State => state.1.start.val)
    I Q 4 step done _ initial (by scalar_tac)
  obtain ⟨out,hout,houtC,houtV⟩ := A.scalar sum hsumC
  refine ⟨out,?_,houtC,?_⟩
  · rw [fold_source,hloop,hout]
    rfl
  · simpa only [hsumV] using houtV

#print axioms fold_source
#print axioms source_success
end AspisR1.CuSavingsLibraSourceScalar
