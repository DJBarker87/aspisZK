import FJc_ArrayUpdateValue
import FIo_RangeNext
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_LibraFrame
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NE)
abbrev State := FIo_RangeNext.Range × Array NE 7#usize

def measure (s : State) : Nat := s.1.end.val-s.1.start.val

def Inv (original : Array NE 7#usize) (s : State) : Prop :=
  ∀ j,j≠4 → FIp_ArrayValue.value s.2 j=FIp_ArrayValue.value original j

theorem step (f : Slice U8) (libra : Array NE 4#usize) (original : Array NE 7#usize)
    (s : State) (inv : Inv original s) (out : ControlFlow State (Array NE 7#usize))
    (run : FIo_Native.weights.Weights.pair_loop16.body f libra s.1 s.2=ok out) :
    match out with
    | .done parts => ∀ j,j≠4 → FIp_ArrayValue.value parts j=FIp_ArrayValue.value original j
    | .cont t => Inv original t ∧ measure t<measure s := by
  rcases s with ⟨iter,parts⟩
  unfold FIo_Native.weights.Weights.pair_loop16.body at run
  obtain ⟨⟨o,cursor⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none => cases Result.ok.inj run;exact inv
  | some i =>
    obtain ⟨old,hold,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨fv,hfv,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨lv,hlv,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨product,hproduct,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨next,hnext,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨updated,hupdated,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases Result.ok.inj run
    have p := FIo_RangeNext.some_next iter cursor i hn
    refine ⟨?_,?_⟩
    · intro j hj
      rw [FJc_ArrayUpdateValue.value parts updated 4#usize next j hupdated]
      have neq : (4#usize).val≠j := by
        have h4 : (4#usize).val=4 := by scalar_tac
        rw [h4]
        exact Ne.symm hj
      rw [if_neg neq]
      exact inv j hj
    · simp only [measure,p.2.1,p.2.2.1];omega

theorem value (f : Slice U8) (libra : Array NE 4#usize) (parts out : Array NE 7#usize)
    (iter : FIo_RangeNext.Range)
    (run : FIo_Native.weights.Weights.pair_loop16 iter f parts libra=ok out) :
    ∀ j,j≠4 → FIp_ArrayValue.value out j=FIp_ArrayValue.value parts j := by
  exact FIo_LoopInvariant.preserve
    (fun s : State=>FIo_Native.weights.Weights.pair_loop16.body f libra s.1 s.2)
    (Inv parts) (fun a=>∀ j,j≠4 → FIp_ArrayValue.value a j=FIp_ArrayValue.value parts j)
    measure (fun s h r hr=>by cases r <;> exact step f libra parts s h _ hr)
    (iter,parts) out (by intro j _;rfl) run

theorem eight_alias (iter : FIo_RangeNext.Range) (f : Slice U8)
    (parts : Array NE 7#usize) (libra : Array NE 4#usize) :
    FIo_Native.weights.Weights.pair_loop8 iter f parts libra=
      FIo_Native.weights.Weights.pair_loop16 iter f parts libra := rfl
#print axioms step
#print axioms value
#print axioms eight_alias
end AspisR1.FJc_LibraFrame
end
