import R1Z.BuilderStdCollect
import R1Z.BuilderRecordsArray

/-! Checked enumeration of a short finite iterator trace. The bound covers
all actual 4/14/4 round-constant groups without normalizing any hash term. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PortEnumerateTrace
open Aeneas Aeneas.Std Result BuilderStdModels
variable {I A : Type}

def pairs (xs : List A) (count : Usize) : List (Usize × A) :=
  match xs with
  | [] => []
  | x::tail => (count,x)::pairs tail (Usize.wrapping_add count 1#usize)

abbrev iterator (it : core.iter.traits.iterator.Iterator I A) :=
  core.iter.traits.iterator.IteratorEnumerate it

theorem trace (it : core.iter.traits.iterator.Iterator I A) (i : I)
    (xs : List A) (ht : FiniteTrace it i xs) (count : Usize)
    (bound : count.val+xs.length ≤ 24) :
    FiniteTrace (iterator it) ⟨i,count⟩ (pairs xs count) := by
  induction ht generalizing count with
  | done i i' hn =>
    apply FiniteTrace.done _ ⟨i',count⟩
    change core.iter.adapters.enumerate.IteratorEnumerate.next it ⟨i,count⟩ = _
    rw [core.iter.adapters.enumerate.IteratorEnumerate.next,hn]
    rfl
  | step i i' x xs hn tail ih =>
    have hc : count.val < 24 := by simp only [List.length_cons] at bound;omega
    have hs : (count+1#usize : Result Usize) ⦃ z => z.val=count.val+1 ⦄ := by
      apply UScalar.add_spec
      scalar_tac
    obtain ⟨next,hnext,hval⟩ := WP.spec_imp_exists hs
    have he : next=Usize.wrapping_add count 1#usize := by
      apply UScalar.eq_of_val_eq
      rw [hval,BuilderRecordsArray.next_val count hc]
    rw [he] at hnext
    apply FiniteTrace.step _ ⟨i',Usize.wrapping_add count 1#usize⟩ (count,x) (pairs xs _)
    · change core.iter.adapters.enumerate.IteratorEnumerate.next it ⟨i,count⟩ = _
      rw [core.iter.adapters.enumerate.IteratorEnumerate.next,hn]
      simp only [bind_tc_ok,hnext]
    · apply ih
      rw [BuilderRecordsArray.next_val count hc]
      simp only [List.length_cons] at bound
      omega

#print axioms trace
end R1Z.PV_Src_PortEnumerateTrace
