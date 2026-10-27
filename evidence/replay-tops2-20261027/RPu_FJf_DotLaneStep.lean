import RPu_FJf_DotLaneDone
set_option autoImplicit false
namespace AspisR1.FJf_DotLaneStep
open Aeneas Aeneas.Std Result ControlFlow
open FJf_DotLane (Dot model)
open FJf_U64Array (cell)
abbrev State := FIo_RangeNext.Range × Dot

def Inv (base : Dot) (raw : Array U64 4#usize) (t : State) : Prop :=
  t.1.end.val=4 ∧ t.1.start.val≤4 ∧ ∀ j,j < 4 → cell t.2.sums j=
    if j < t.1.start.val then model base raw j else cell base.sums j

def Post (base : Dot) (raw : Array U64 4#usize) (out : Dot) : Prop :=
  ∀ j,j < 4 → cell out.sums j=model base raw j

def measure (t : State) : Nat := t.1.end.val-t.1.start.val

theorem step (base : Dot) (raw : Array U64 4#usize) (t : State)
    (inv : Inv base raw t) (out : ControlFlow State Dot)
    (run : FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw t.1 t.2=ok out) :
    match out with
    | .done f => Post base raw f
    | .cont next => Inv base raw next ∧ measure next < measure t := by
  rcases t with ⟨iter,dot⟩
  dsimp only [Inv] at inv
  cases out with
  | done f =>
    obtain ⟨stop,rfl⟩ := FJf_DotLaneDone.done raw iter dot f run
    have eq : iter.start.val=4 := by omega
    intro j hj
    have hv := inv.2.2 j hj
    simpa only [eq,if_pos hj] using hv
  | cont next =>
    rcases next with ⟨cursor,f⟩
    obtain ⟨he,hs,hm,hv⟩ := FJf_DotLane.value raw iter cursor dot f run
    dsimp only [Inv]
    refine ⟨⟨by rw [he];exact inv.1,by omega,?_⟩,?_⟩
    · intro j hj
      rw [hv]
      by_cases hw : iter.start.val=j
      · rw [if_pos hw,if_pos (by omega)]
        unfold model
        rw [inv.2.2 j hj,if_neg (by omega)]
      · rw [if_neg hw,inv.2.2 j hj]
        have eq : (j < iter.start.val) ↔ (j < cursor.start.val) := by omega
        simp only [eq]
    · simp only [measure,he,hs];omega
#print axioms step
end AspisR1.FJf_DotLaneStep
