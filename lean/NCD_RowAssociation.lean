import NCD_KMX_CopyMeaning
set_option autoImplicit false
namespace NCD_RowAssociation
/-- Selected local observations of one vector carrier, including exact extent.
No successful model call or whole output equality is supplied. -/
structure Cells {α : Type} (before after extra : List α) : Prop where
  size : after.length=before.length+extra.length
  retained : ∀ i, i<before.length → after[i]?=before[i]?
  written : ∀ j, j<extra.length → after[before.length+j]?=extra[j]?

theorem appended {α : Type} {before after extra : List α}
    (cells : Cells before after extra) : after=before++extra := by
  apply List.ext_getElem
  · simpa only [List.length_append] using cells.size
  · intro i hi hj
    have same : after[i]?=(before++extra)[i]? := by
      rw [List.getElem?_append]
      by_cases old : i<before.length
      · simpa only [if_pos old] using cells.retained i old
      · rw [if_neg old]
        have atNew := cells.written (i-before.length) (by have h:=cells.size;omega)
        simpa only [Nat.add_sub_of_le (Nat.le_of_not_gt old)] using atNew
    rw [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj] at same
    exact Option.some.inj same

/-- Reuse KMX's append semantics for the SAME flat row and line-z value.
Native trace existence, allocation ownership and metadata are not inferred. -/
theorem same_row {α : Type} (beforeFlat afterFlat beforeZ afterZ row : List α)
    (width : row.length=5)
    (flat : Cells beforeFlat afterFlat row)
    (z : Cells beforeZ afterZ [row[4]'(by omega)]) :
    KMX_CopyMeaning.appendLoop beforeFlat row=afterFlat ∧
    KMX_CopyMeaning.appendLoop beforeZ [row[4]'(by omega)]=afterZ := by
  rw [KMX_CopyMeaning.append_spec,KMX_CopyMeaning.append_spec]
  exact ⟨(appended flat).symm,(appended z).symm⟩
#print axioms appended
#print axioms same_row
end NCD_RowAssociation
