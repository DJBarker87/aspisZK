import NDO_FIv_HornerTotal
import NDO_FIv_Horner4Total
import RPv_FIv_PreparedNewTotal
import RPv_FIv_CompositionValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_FoldsTotal
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)

def body (semantic : Array NQ 24#usize) (poseidon : Array NQ 4#usize) (theta seed : NQ) : Result NQ := do
  let prepared ← FIq_Native.field.PreparedQm31Multiplier.new theta
  let middle ← FIq_Native.pool_v1.pair_forest_semantic_terminal.composition_parts_loop0 ⟨semantic.val⟩ prepared seed
  FIq_Native.pool_v1.pair_forest_semantic_terminal.composition_parts_loop1 ⟨poseidon.val⟩ prepared middle

theorem value (semantic : Array NQ 24#usize) (poseidon : Array NQ 4#usize) (theta seed : NQ)
    (ht : Canon theta) (hs : Canon seed)
    (hsem : ∀ x∈semantic.val,Canon x) (hpos : ∀ x∈poseidon.val,Canon x) :
    ∃ out, body semantic poseidon theta seed=ok out ∧ Canon out ∧
      decode out=FIv_CompositionValue.polynomial (decode theta) semantic poseidon seed := by
  obtain ⟨p,hp,hvalid⟩ := FIv_PreparedNewTotal.value theta ht
  obtain ⟨middle,hm,hmc,hmv⟩ := FIv_HornerTotal.value semantic.val.reverse p theta seed ht hs hvalid
    (fun x hx=>hsem x (List.mem_reverse.mp hx))
  obtain ⟨out,ho,hoc,hov⟩ := FIv_Horner4Total.value poseidon.val.reverse p theta middle ht hmc hvalid
    (fun x hx=>hpos x (List.mem_reverse.mp hx))
  simp only [List.reverse_reverse] at hm ho
  change FIq_Native.pool_v1.pair_forest_semantic_terminal.composition_parts_loop0 ⟨semantic.val⟩ p seed=ok middle at hm
  change FIq_Native.pool_v1.pair_forest_semantic_terminal.composition_parts_loop1 ⟨poseidon.val⟩ p middle=ok out at ho
  refine ⟨out,?_,hoc,?_⟩
  · unfold body
    rw [hp,bind_tc_ok,hm,bind_tc_ok,ho]
  · rw [hov,hmv,FIv_HornerAlgebra.four,FIv_HornerAlgebra.reversed]
    have len24 := semantic.property
    have len4 := poseidon.property
    change semantic.val.length=24 at len24
    change poseidon.val.length=4 at len4
    rw [len24,len4]
    unfold FIv_CompositionValue.polynomial
    ring
#print axioms value
end AspisR1.FIv_FoldsTotal
end
