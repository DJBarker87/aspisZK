import Aeneas.Std

/-! Pure backing-list update fact used for the length-four copy path. -/
namespace AspisR1.Qm31PackBase4SliceFacts

theorem setSlice_zero_eq_source {α : Type} (backing source : List α)
    (hbacking : backing.length = 4) (hsource : source.length = 4) :
    backing.setSlice! 0 source = source := by
  simp [List.setSlice!, hbacking, hsource]

#print axioms setSlice_zero_eq_source

end AspisR1.Qm31PackBase4SliceFacts
