import AspisR1CuRhoInitRow.Funs
import CuSavingsRhoPush
import CuSavingsRhoSourceFinish

/-! Exact execution of the extracted four-word initialization assignment.
The list initialization below supplies its canonical round-trip and initial
overflow invariant. It is a semantic model of the surrounding zip, not an
extraction of new/zip or a theorem about heap allocation. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoInitRow
open Aeneas Aeneas.Std Result
open AspisR1CuRho
open CuSavingsRhoValue CuSavingsRhoPush CuSavingsRhoFinishModel
open AspisV8R17.RawReducer CuSavingsResidues

def carrier (w : field.QM31) : AspisR1CuRhoInitRow.field.QM31 :=
  {c0 := {a := w.c0.a,b := w.c0.b},c1 := {a := w.c1.a,b := w.c1.b}}

def initialRow (w : field.QM31) : Array U64 4#usize :=
  Array.make 4#usize [UScalar.cast .U64 w.c0.a,UScalar.cast .U64 w.c0.b,
    UScalar.cast .U64 w.c1.a,UScalar.cast .U64 w.c1.b]

theorem row_success (w : field.QM31) :
    AspisR1CuRhoInitRow.row (carrier w) = .ok (initialRow w) := by
  simp only [AspisR1CuRhoInitRow.row,carrier,lift,bind_tc_ok]
  rfl

theorem word_initial_val (w : field.QM31) (j : Fin 4) :
    (wordAt (initialRow w) j).val = (wordAt (powerLimbs w) j).val := by
  have hword : wordAt (initialRow w) j = UScalar.cast .U64 (wordAt (powerLimbs w) j) := by
    change ((powerLimbs w).val.map (UScalar.cast .U64))[j.val]'_ = _
    simp only [List.getElem_map,wordAt]
  rw [hword,ExtractedCurrentReducer.cast_widen_value]

def Canonical (w : field.QM31) : Prop :=
  ∀ j : Fin 4, (wordAt (powerLimbs w) j).val < P

theorem initial_bound (w : field.QM31) (hc : Canonical w) (j : Fin 4) :
    RhoBound (wordAt (initialRow w) j).val 0 := by
  rw [word_initial_val]
  have h := hc j
  simp only [RhoBound,Nat.zero_mod,Nat.zero_mul,Nat.add_zero]
  change (wordAt (powerLimbs w) j).val < 17179869184
  change (wordAt (powerLimbs w) j).val < 2147483647 at h
  omega

theorem canonical_cast (x : U32) (hx : x.val < P) :
    canonicalWord (UScalar.cast .U64 x) = x := by
  apply UScalar.eq_of_val_eq
  rw [canonicalWord_val,ExtractedCurrentReducer.cast_widen_value,Nat.mod_eq_of_lt hx]

theorem canonical_initial (w : field.QM31) (hc : Canonical w) :
    canonicalValue (initialRow w) = w := by
  have ha := hc 0
  have hb := hc 1
  have hc' := hc 2
  have hd := hc 3
  change w.c0.a.val < P at ha
  change w.c0.b.val < P at hb
  change w.c1.a.val < P at hc'
  change w.c1.b.val < P at hd
  change {c0 := {a := canonicalWord (UScalar.cast .U64 w.c0.a),
                b := canonicalWord (UScalar.cast .U64 w.c0.b)},
          c1 := {a := canonicalWord (UScalar.cast .U64 w.c1.a),
                b := canonicalWord (UScalar.cast .U64 w.c1.b)}} = w
  rw [canonical_cast _ ha,canonical_cast _ hb,canonical_cast _ hc',canonical_cast _ hd]

def initialState (weights : Slice field.QM31) : verifier.BatchedWeights :=
  {«raw» := ⟨weights.val.map initialRow,by
    simpa only [List.length_map] using weights.property⟩,terms := 0#usize}

theorem initial_finish (weights : Slice field.QM31)
    (hc : ∀ w ∈ weights.val,Canonical w) :
    AspisR1CuRhoSource.verifier.BatchedWeights.finish (initialState weights) weights =
      .ok weights := by
  rw [CuSavingsRhoSourceFinish.source_success _ _ (by
    simp only [initialState,List.length_map])]
  apply congrArg Result.ok
  apply Subtype.ext
  change (weights.val.map initialRow).map canonicalValue = weights.val
  rw [List.map_map]
  exact List.map_id' (fun w hw => canonical_initial w (hc w hw))

#print axioms row_success
#print axioms word_initial_val
#print axioms initial_bound
#print axioms canonical_initial
#print axioms initial_finish
end AspisR1.CuSavingsRhoInitRow
