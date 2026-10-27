import KSC1_IteratorProbe
import KSC1_ReverseProbe
import KSC1_P7
import KSC1_NeP7
import KSC1_Vec
import KSC1_FnState
import KSC1_FnProbe
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace KSC1.Final

theorem singleton_counterexample :
    (do let (v,_) ← KSA_Isolated.XRn_Join_nextBackPair KSC1.spent; ok v) = ok (some 7#u8) ∧
    (do let (_,s,_) ← core.slice.iter.IteratorIterMut.next KSC1.singleton
        let (v,_) ← KSA_Isolated.XRn_Join_nextBackPair s
        ok v) ≠ ok none :=
  ⟨KSC1.back_repeats_spent, KSC1.mixed_direction_not_exhausted⟩

#print axioms singleton_counterexample
end KSC1.Final
#print axioms KSC1.front_consumes_singleton
#print axioms KSC1.back_repeats_spent
#print axioms KSC1.mixed_direction_not_exhausted
#print axioms KSC1.reverse_repeats_spent
#print axioms KSC1.reverse_restores_changed_element
#print axioms KSC1.reverse_empty
#print axioms KSC1.P7.slice_array_eq
#print axioms KSC1.P7.slice_array_ne
#print axioms KSC1.P7.next_projection
#print axioms KSC1.P7.restored_array
#print axioms KSC1.P7.any_not_all
#print axioms KSC1.P7.slice_array_ne_p7
#print axioms KSC1.vec_is_empty
#print axioms KSC1.FnState.indexed_eq
#print axioms KSC1.FnState.from_fn_state_eq
#print axioms KSC1.FnProbe.add_value
#print axioms KSC1.FnProbe.state_sequence
#print axioms KSC1.FnProbe.empty_state
#print axioms KSC1.FnProbe.panic_at_two
#print axioms KSC1.FnProbe.state_array
#print axioms KSC1.FnProbe.from_fn_array
#print axioms KSC1.FnProbe.map_sequence
