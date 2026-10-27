import FJl_TermRead
import FIo_LoopInvariant
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_InnerReads
open Aeneas Aeneas.Std Result ControlFlow
open FJi_Accumulations
abbrev State := FIo_RangeNext.Range × Sums
def Read (q : Array U8 608#usize) (slot : Usize) (n : Nat) : Prop :=
  ∃ term x,term.val=n ∧ JFr_TX2_ScalarRead.read q slot term=ok x

theorem value (q : Array U8 608#usize) (g : Array NE 29#usize) (slot : Usize)
    (iter : FIo_RangeNext.Range) (seed out : Sums)
    (ordered : iter.start.val≤iter.end.val) (small : iter.end.val≤26)
    (run : FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0 iter q g slot seed=ok out) :
    ∀ n,iter.start.val≤n → n<iter.end.val → Read q slot n := by
  let inv : State → Prop := fun s=>s.1.end.val=iter.end.val ∧ iter.start.val≤s.1.start.val ∧
    s.1.start.val≤iter.end.val ∧ ∀ n,iter.start.val≤n → n<s.1.start.val → Read q slot n
  let post : Sums → Prop := fun _=>∀ n,iter.start.val≤n → n<iter.end.val → Read q slot n
  apply FIo_LoopInvariant.preserve
    (fun s : State=>FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0.body q g slot s.1 s.2)
    inv post (fun s=>s.1.end.val-s.1.start.val) ?_ (iter,seed) out ?_ run
  · intro s h result called
    rcases s with ⟨cursor,limbs⟩
    obtain ⟨ending,lower,upper,reads⟩ := h
    cases result with
    | done result =>
      obtain ⟨halt,same⟩ := FJi_TermValue.done q g slot cursor limbs result called
      intro n hn hn'
      exact reads n hn (by omega)
    | cont next =>
      rcases next with ⟨cursor1,limbs1⟩
      obtain ⟨he,inc,active,hvalues⟩ := FJi_TermValue.value q g slot cursor cursor1 limbs limbs1 (by omega) called
      have reached := FJl_TermRead.value q g slot cursor cursor1 limbs limbs1 called
      refine ⟨⟨by simpa only [he] using ending,by omega,by omega,?_⟩,?_⟩
      · intro n hn hn'
        by_cases old : n<cursor.start.val
        · exact reads n hn old
        · have same : n=cursor.start.val := by omega
          rw [same]
          exact reached
      · dsimp only
        rw [he,inc]
        omega
  · refine ⟨rfl,Nat.le_refl _,ordered,?_⟩
    intro n hn hn'
    omega
#print axioms value
end AspisR1.FJl_InnerReads
end
