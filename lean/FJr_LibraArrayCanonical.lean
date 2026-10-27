import FJc_LibraFrame
import FIo_WideMulValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_LibraArrayCanonical
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NE)
open FJc_LibraFrame (State measure)

theorem step (f : Slice U8) (libra : Array NE 4#usize) (cl : FIo_ArrayCanon.Holds libra)
    (s : State) (cb : FIo_ArrayCanon.Holds s.2) (result : ControlFlow State (Array NE 7#usize))
    (run : FIo_Native.weights.Weights.pair_loop16.body f libra s.1 s.2=ok result) :
    match result with
    | .done out=>FIo_ArrayCanon.Holds out
    | .cont next=>FIo_ArrayCanon.Holds next.2 ∧ measure next<measure s := by
  rcases s with ⟨iter,parts⟩
  unfold FIo_Native.weights.Weights.pair_loop16.body at run
  obtain ⟨⟨o,cursor⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none=>cases Result.ok.inj run;exact cb
  | some j=>
    obtain ⟨old,hold,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨fv,hfv,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨lv,hlv,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨product,hproduct,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨sum,hsum,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨updated,hupdated,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases Result.ok.inj run
    have cp := FIo_WideMulValues.mul fv lv product (FIo_FieldCanonical.field f j fv hfv)
      (FIo_ArrayCanon.read libra j lv cl hlv) hproduct
    have cs := FIo_WideValues.add old product sum (FIo_ArrayCanon.read parts 4#usize old cb hold) cp.1 hsum
    have pr := FIo_RangeNext.some_next iter cursor j hn
    refine ⟨FIo_ArrayCanon.update parts updated 4#usize sum cb cs.1 hupdated,?_⟩
    simp only [FJc_LibraFrame.measure,pr.2.1,pr.2.2.1]
    omega

theorem value (f : Slice U8) (libra : Array NE 4#usize) (cl : FIo_ArrayCanon.Holds libra)
    (iter : FIo_RangeNext.Range) (parts out : Array NE 7#usize) (cb : FIo_ArrayCanon.Holds parts)
    (run : FIo_Native.weights.Weights.pair_loop16 iter f parts libra=ok out) : FIo_ArrayCanon.Holds out := by
  exact FIo_LoopInvariant.preserve
    (fun s : State=>FIo_Native.weights.Weights.pair_loop16.body f libra s.1 s.2)
    (fun s=>FIo_ArrayCanon.Holds s.2) FIo_ArrayCanon.Holds measure
    (fun s h r hr=>by cases r <;> exact step f libra cl s h _ hr) (iter,parts) out cb run

#print axioms step
#print axioms value
end AspisR1.FJr_LibraArrayCanonical
end
