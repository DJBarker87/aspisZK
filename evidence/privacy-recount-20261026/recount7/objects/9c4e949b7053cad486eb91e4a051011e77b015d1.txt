import R1Z.BuilderSliceCollect
import Aeneas

/-! Finite enumeration with a checked source counter. The bound20 covers the
actual4/14/4 round tables and rules out counter overflow; no permutation is
unfolded and the underlying Iterator.next trace remains explicit. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_EnumerateTrace
open Aeneas Aeneas.Std Result BuilderStdModels
variable {I A : Type}

def labels (count : Usize) : List A → List (Usize × A)
  | [] => []
  | x::xs => (count,x) :: labels (Usize.wrapping_add count 1#usize) xs

abbrev enumerated (it : core.iter.traits.iterator.Iterator I A) :=
  core.iter.traits.iterator.IteratorEnumerate it

theorem checked_next (count : Usize) (hc : count.val < 24) :
    (count + 1#usize : Result Usize) = ok (Usize.wrapping_add count 1#usize) := by
  have hv := BuilderRecordsArray.next_val count hc
  have bound : count.val + (1#usize : Usize).val ≤ Usize.max := by
    change count.val+1 ≤ Usize.max
    rw [← hv]
    scalar_tac
  obtain ⟨z,hz,hzv⟩ : ∃ z : Usize,
      (count+1#usize : Result Usize)=ok z ∧ z.val=count.val+1 := by
    apply WP.spec_imp_exists
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq] using bound
  have he : z=Usize.wrapping_add count 1#usize :=
    UScalar.eq_of_val_eq (hzv.trans hv.symm)
  simpa only [he] using hz

theorem trace (it : core.iter.traits.iterator.Iterator I A)
    (i : I) (xs : List A) (ht : FiniteTrace it i xs)
    (count : Usize) (bound : count.val+xs.length ≤ 20) :
    FiniteTrace (enumerated it) ⟨i,count⟩ (labels count xs) := by
  induction ht generalizing count with
  | done i i' hn =>
    apply FiniteTrace.done _ ⟨i',count⟩
    simp only [enumerated,core.iter.adapters.enumerate.IteratorEnumerate.next,hn,bind_tc_ok]
  | step i i' x xs hn tail ih =>
    have hc : count.val < 24 := by simp only [List.length_cons] at bound;omega
    have hv := BuilderRecordsArray.next_val count hc
    change FiniteTrace _ _ ((count,x)::labels (Usize.wrapping_add count 1#usize) xs)
    apply FiniteTrace.step _ ⟨i',Usize.wrapping_add count 1#usize⟩
    · simp only [enumerated,core.iter.adapters.enumerate.IteratorEnumerate.next,
        hn,bind_tc_ok,checked_next count hc]
    · apply ih
      rw [hv]
      simp only [List.length_cons] at bound
      omega

#print axioms checked_next
#print axioms trace
end R1Z.PV_RunJoin_EnumerateTrace
