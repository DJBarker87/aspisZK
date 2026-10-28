import NBJ_Address

set_option autoImplicit false
namespace AspisR1.NBJ_WindowCover

/-- The finite physical read image; surrounding bytes are unrestricted. -/
def image {α : Type} (memory : Nat → α) (base width : Nat) : List α :=
  List.ofFn (fun k : Fin width => memory (base+k.val))

/-- Twenty-six independently checked32-byte windows cover every opening byte.
No final whole-opening equality is a hypothesis. -/
theorem opening_cover {α : Type} (native model : Nat → α) (base : Nat)
    (windows : ∀ w, w < 26 → ∀ c, c < 32 →
      native (base+32*w+c) = model (base+32*w+c)) :
    image native base 832 = image model base 832 := by
  apply List.ext_getElem
  · simp only [image,List.length_ofFn]
  · intro k hn hm
    have bound : k < 832 := by simpa only [image,List.length_ofFn] using hn
    have wb : k/32 < 26 := by omega
    have cb : k%32 < 32 := Nat.mod_lt k (by decide)
    have address : base+32*(k/32)+k%32 = base+k := by omega
    have same := windows (k/32) wb (k%32) cb
    simpa only [image,List.getElem_ofFn,address] using same

/-- Relocation is compositional: one local window is independent of its
absolute physical base once the scalar address has been associated. -/
theorem relocation {α : Type} (memory : Nat → α) (base width : Nat) :
    image (fun c => memory (base+c)) 0 width = image memory base width := by
  unfold image
  congr 1
  funext k
  simp only [Nat.zero_add]

#print axioms opening_cover
#print axioms relocation
end AspisR1.NBJ_WindowCover
