import LPm_CheckpointDomains
set_option autoImplicit false
namespace AspisR1.LPm_FieldCarriers
open Aeneas Aeneas.Std Result OraclePortCkptAbi2Extracted
open CheckpointBytes5Writer CheckpointBytesBody

/-- A fixed array's source traversal list is determined by ALL of its actual
indexed values, not a second array with the same length. -/
theorem indexed_values {α : Type} (xs : List α) (n : Nat) (size : xs.length=n) :
    (List.ofFn fun j : Fin n => xs[j.val]'(by rw [size]; exact j.isLt)) = xs := by
  apply List.ext_getElem
  · simp [size]
  · intro i hi hj
    simp only [List.getElem_ofFn]

/-- The scalar-level port used by the native iterator gates identifies the
ENTIRE QM31 carrier. Equal natural words are sufficient even when raw limbs
are noncanonical. -/
theorem q_values_injective (x y : aspis_core.field.QM31)
    (a : x.c0.a.val=y.c0.a.val) (b : x.c0.b.val=y.c0.b.val)
    (c : x.c1.a.val=y.c1.a.val) (d : x.c1.b.val=y.c1.b.val) : x=y := by
  have ha := UScalar.eq_of_val_eq a
  have hb := UScalar.eq_of_val_eq b
  have hc := UScalar.eq_of_val_eq c
  have hd := UScalar.eq_of_val_eq d
  cases x with
  | mk x0 x1 =>
    cases y with
    | mk y0 y1 =>
      cases x0; cases x1; cases y0; cases y1
      simp_all only

/-- The native semantic_alpha by-value array iterator has exactly these ten
fields; this is the carrier consumed by the inherited arbitrary-list fold. -/
theorem semantic_values (p : Prepared) (a : Accumulator)
    (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22,
      (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144) :
    List.ofFn (fields p a size qb).semanticAlpha = p.semantic_alpha.val := by
  exact indexed_values _ 10 p.semantic_alpha.property

/-- Join the source's nested two-point x/y traversal to the exact four
coordinate fields of the SAME checkpoint input. -/
theorem coordinate_values (p : Prepared) (a : Accumulator)
    (size : a.weights.val.length = 64)
    (qb : ∀ j : Fin 22,
      (p.queries.val[j.val]'(by simpa [p.queries.property] using j.isLt)).val < 262144) :
    List.ofFn (fields p a size qb).coordinates = p.z.val.flatMap (fun z => [z.x,z.y]) := by
  rw [← indexed_values p.z.val 2 p.z.property]
  simp only [List.ofFn_succ,List.ofFn_zero,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.cons_append,List.nil_append]
  rfl

#print axioms indexed_values
#print axioms q_values_injective
#print axioms semantic_values
#print axioms coordinate_values
end AspisR1.LPm_FieldCarriers
