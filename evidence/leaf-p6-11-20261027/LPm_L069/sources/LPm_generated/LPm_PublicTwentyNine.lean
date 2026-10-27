import LPm_PublicFold
set_option autoImplicit false
namespace AspisR1.LPm_PublicTwentyNine
open Aeneas Aeneas.Std Result LPi_FieldValues LPm_RawPort LPm_PublicFold

def zero : Native :=
  ⟨⟨Array.repeat 4#usize 0#u64⟩,⟨Array.repeat 4#usize 0#u64⟩,0#usize⟩

theorem source_new : FIo_Native.fast_pairing.EbyKDot.new=ok zero := rfl

theorem initial_bound : Bounded zero 0 := by
  refine ⟨rfl,?_,?_⟩
  all_goals
    intro x hx
    simp only [zero,Array.repeat,List.mem_replicate] at hx
    rcases hx with ⟨_,rfl⟩
    simp only [Nat.zero_mul]
    decide

/-- ONE theorem applies to each of the six actual point traces. The local
native calls determine the value; no public field-sum equality is assumed. -/
theorem source (xs : List (NE×NQ)) (out : Native) (size : xs.length=29)
    (tr : Trace xs zero out) :
    Bounded out 29 ∧ meaning out=fold (meaning zero) xs := by
  have result := trace_value tr 0 (by omega) initial_bound
  simpa only [size,Nat.zero_add] using result

#print axioms source_new
#print axioms initial_bound
#print axioms source
end AspisR1.LPm_PublicTwentyNine
