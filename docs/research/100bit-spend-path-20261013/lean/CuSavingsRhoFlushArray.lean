import CuSavingsRhoFlushLoop
import CuSavingsRhoState

/-! Bind the actual array iterator conversion and handback to the checked flush
loop. Its output array is the pointwise partial fold of ALL four raw limbs. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoFlushArray
open Aeneas Aeneas.Std Result
open AspisR1CuRho
open AspisR1.CuSavingsRhoPushStep
open AspisR1.CuSavingsRhoValue
open AspisR1.CuSavingsRhoFlushModel
open AspisV8R17.RawReducer

def initialIter (raw : Raw4) : Iter := {slice := Array.to_slice raw}

def foldedArray (raw : Raw4) : Raw4 :=
  ⟨raw.val.map foldWord,by simpa only [List.length_map] using raw.property⟩

theorem model_array (raw : Raw4) :
    Array.from_slice raw (modelIter (initialIter raw)).slice = foldedArray raw := by
  apply Subtype.ext
  have hlen : (modelIter (initialIter raw)).slice.val.length = (4#usize).val := by
    change (raw.val.map foldWord).length = (4#usize).val
    simpa only [List.length_map] using raw.property
  rw [Array.from_slice_val raw _ hlen]
  rfl

theorem source_success (raw : Raw4) :
    ∃ (last : Iter) (back : Iter → Iter),
      verifier.BatchedWeights.push_loop1 (initialIter raw) (fun out => out) =
        .ok (last,back) ∧
      Array.from_slice raw (back last).slice = foldedArray raw := by
  obtain ⟨last,back,hrun,hmodel⟩ := AspisR1.CuSavingsRhoFlushLoop.source_success
    (initialIter raw) (by change 0 ≤ raw.val.length;omega)
  refine ⟨last,back,hrun,?_⟩
  rw [hmodel]
  exact model_array raw

theorem word_folded (raw : Raw4) (j : Fin 4) :
    wordAt (foldedArray raw) j = foldWord (wordAt raw j) := by
  simp only [wordAt,foldedArray,List.getElem_map]

theorem word_folded_val (raw : Raw4) (j : Fin 4) :
    (wordAt (foldedArray raw) j).val = foldBits (wordAt raw j).val := by
  rw [word_folded,foldWord_val]

#print axioms model_array
#print axioms source_success
#print axioms word_folded_val
end AspisR1.CuSavingsRhoFlushArray
