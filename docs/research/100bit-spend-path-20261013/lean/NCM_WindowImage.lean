import NCE_OpeningCuts

set_option autoImplicit false
namespace AspisR1.NCM_WindowImage

/-- Convert the checked per-byte read image to the actual bounded slice
value. The bound is proved from the source range, never from native success. -/
theorem image_slice {A : Type} [Inhabited A] (xs : List A) (base width : Nat)
    (bound : base+width ≤ xs.length) :
    NBJ_WindowCover.image (fun k => xs[k]!) base width = (xs.drop base).take width := by
  apply List.ext_getElem
  · simp only [NBJ_WindowCover.image,List.length_ofFn,List.length_take,List.length_drop]
    omega
  · intro k left right
    have kb : k < width := by simpa only [NBJ_WindowCover.image,List.length_ofFn] using left
    simp only [NBJ_WindowCover.image,List.getElem_ofFn,List.getElem_take,List.getElem_drop]
    exact getElem!_pos xs (base+k) (by omega)

#print axioms image_slice
end AspisR1.NCM_WindowImage
