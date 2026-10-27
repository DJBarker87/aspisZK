import KSA_XRn_Join_ABI
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace KSC1
open KSA_Isolated

def singleton : core.slice.iter.IterMut U8 := {slice := (Array.make 1#usize [7#u8]).to_slice}
def spent : core.slice.iter.IterMut U8 := {slice := singleton.slice, i := 1}

theorem front_consumes_singleton :
    (do let (_,s,_) ← core.slice.iter.IteratorIterMut.next singleton; ok s) = ok spent := by rfl

theorem back_repeats_spent :
    (do let (v,_) ← XRn_Join_nextBackPair spent; ok v) = ok (some 7#u8) := by rfl

theorem mixed_direction_not_exhausted :
    (do let (_,s,_) ← core.slice.iter.IteratorIterMut.next singleton
        let (v,_) ← XRn_Join_nextBackPair s
        ok v) ≠ ok none := by
  intro h
  have e : (some 7#u8 : Option U8) = none := Result.ok.inj h
  cases e

#print axioms front_consumes_singleton
#print axioms back_repeats_spent
#print axioms mixed_direction_not_exhausted
end KSC1
