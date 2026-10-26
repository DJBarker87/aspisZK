import FIy_OccupancySource
import FIy_OccupancyClosed
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_OccupancyMeaning
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)

def model (input output : K) (expected : Nat) (a : Nat → K) : Fin (12#usize).val → K := fun j=>
  if j.val=11 then FIy_OccupancyTail.scalar input output (a 0) (1-a 0) expected a
  else if 3≤j.val ∧ j.val<11 then (input+output)*((1-a 0)*a (j.val-1))
  else FIy_OccupancyPrefix.model input output a j

theorem value (input output : NQ) (expected : U32) (opened : Array NQ 16#usize)
    (out : Array NQ 12#usize) (hi : Canon input) (ho : Canon output)
    (he : expected.val<FIw_ScalarArithmetic.P) (ha : canonical opened)
    (success : pool_v1.pair_forest_semantic_terminal.occupancy_lanes_literal input output expected opened=ok out) :
    canonical out ∧ decoded out=model (decode input) (decode output) expected.val (FIv_NativeArray.value opened) := by
  rw [FIy_OccupancySource.factor] at success
  obtain ⟨⟨occ,m,b,initial⟩,hprefix,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨middle,hmiddle,tail⟩ := FIv_Map.bind_success _ _ _ success
  have prefix := FIy_OccupancyPrefix.value input output opened occ m b initial hi ho ha hprefix
  have loop := FIy_OccupancyLoop.value 8 ⟨0#usize,poseidon2.DIGEST_ELEMS⟩ opened m b initial middle
    (by rw [poseidon2.DIGEST_ELEMS];rfl) (by rfl) ha prefix.2.1 prefix.2.2.1 prefix.2.2.2.1 hmiddle
  have ending := FIy_OccupancyTail.value input output occ m expected opened middle out hi ho prefix.1 prefix.2.1
    he ha loop.1 tail
  refine ⟨ending.1,?_⟩
  rw [ending.2,loop.2,prefix.2.2.2.2.2.2.2]
  funext j
  have hidx : (0#usize).val=0 := rfl
  have h11 : (j=(⟨11,by decide⟩ : Fin (12#usize).val)) ↔ j.val=11 := Fin.ext_iff
  by_cases hj : j.val=11
  · have ej : j=(⟨11,by decide⟩ : Fin (12#usize).val) := h11.mpr hj
    rw [ej,Function.update_self]
    simp only [model,if_pos rfl,FIy_OccupancyTail.scalar,prefix.2.2.2.2.1,prefix.2.2.2.2.2.1]
  · rw [Function.update_of_ne (fun eq=>hj (h11.mp eq)),FIy_OccupancyClosed.value]
    simp only [hidx,Nat.add_zero,prefix.2.2.2.2.2.1,prefix.2.2.2.2.2.2.1,model,if_neg hj]
#print axioms value
end AspisR1.FIy_OccupancyMeaning
end
