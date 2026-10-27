import FIw_ArrayValue
import FIv_CompositionValue
import FIw_CompositionOrigins
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJk_HornerValue
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon decode K)
open FIw_ArrayValue (canonical)
/-- The composition cut's OWN arrays and copy result, without selecting a second run. -/
theorem value (semantic : Array field.QM31 24#usize) (poseidon : Array field.QM31 4#usize)
    (prepared : field.PreparedQm31Multiplier) (theta seed middle comp : field.QM31)
    (iterator : core.iter.adapters.rev.Rev (FIq_Native.core.array.iter.IntoIter field.QM31 24#usize))
    (iterator1 : core.iter.adapters.rev.Rev (FIq_Native.core.array.iter.IntoIter field.QM31 4#usize))
    (ht : Canon theta) (hs : Canon seed) (hc : canonical semantic) (hp : canonical poseidon)
    (prep : field.PreparedQm31Multiplier.new theta=ok prepared)
    (hi : iterator.iter=semantic.val) (hi1 : iterator1.iter=poseidon.val)
    (run : pool_v1.pair_forest_semantic_terminal.composition_parts_loop0 iterator prepared seed=ok middle)
    (run1 : pool_v1.pair_forest_semantic_terminal.composition_parts_loop1 iterator1 prepared middle=ok comp) :
    Canon comp ∧ decode comp=FIv_CompositionValue.polynomial (decode theta) semantic poseidon seed := by
  have pp := FIv_PreparedNew.valid theta prepared ht prep
  have it : iterator=⟨semantic.val⟩ := by cases iterator; cases hi; rfl
  have it1 : iterator1=⟨poseidon.val⟩ := by cases iterator1; cases hi1; rfl
  rw [it] at run
  rw [it1] at run1
  have mid := FIv_Horner24.value semantic.val.reverse prepared theta seed middle ht hs pp
    (fun x hx=>hc x (List.mem_reverse.mp hx)) (by simpa only [List.reverse_reverse] using run)
  have fin := FIv_Horner4.value poseidon.val.reverse prepared theta middle comp ht mid.1 pp
    (fun x hx=>hp x (List.mem_reverse.mp hx)) (by simpa only [List.reverse_reverse] using run1)
  refine ⟨fin.1,?_⟩
  rw [fin.2,mid.2,FIv_HornerAlgebra.four,FIv_HornerAlgebra.reversed]
  have len24 := semantic.property
  have len4 := poseidon.property
  change semantic.val.length=24 at len24
  change poseidon.val.length=4 at len4
  rw [len24,len4]
  unfold FIv_CompositionValue.polynomial
  ring
#print axioms value
end AspisR1.FJk_HornerValue
end
