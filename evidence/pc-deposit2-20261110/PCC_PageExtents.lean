import PCC_PageImage
set_option autoImplicit false
namespace PCC
open PCA

theorem page_image_length (args : PageArgs) : (pageImage args).length = 8256 := by
  simp only [pageImage, List.length_map, List.length_range]

/-- One arbitrary root window, for the required later KMX composition. -/
theorem root_window_extent (n slot : Nat) (hn : n ≤ 256) (hs : slot < n) :
    64 ≤ 64+slot*32 ∧ 64+slot*32+32 ≤ 8256 := by omega

theorem root_windows_disjoint (i j : Nat) (h : i < j) :
    64+i*32+32 ≤ 64+j*32 := by omega

#print axioms page_image_length
#print axioms root_window_extent
#print axioms root_windows_disjoint
end PCC
