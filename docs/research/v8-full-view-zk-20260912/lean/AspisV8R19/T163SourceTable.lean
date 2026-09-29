/- Generated from source table SHA256 f3ff6a2dea690ebabfe19243186d96a3c0c4bb64beb2bfd601ae1efccd45bb2d.
Only small index lookups are reduced. The fixed tail uses a symbolic lemma. -/
import AspisV8R19.ResidualPins
namespace AspisR19.T163SourceTable
def forwardBlocks : List (List Nat) := [[13, 14, 15, 29, 30, 31, 45, 46, 47, 61, 62, 63, 77, 78, 79, 93, 94, 95, 109, 110, 111, 125, 126, 127, 141, 142, 143, 157, 158, 159, 173, 174], [175, 189, 190, 191, 205, 206, 207, 221, 222, 223, 237, 238, 239, 253, 254, 255, 269, 270, 271, 285, 286, 287, 301, 302, 303, 317, 318, 319, 333, 334, 335, 349], [350, 351, 365, 366, 367, 381, 382, 383, 397, 398, 399, 413, 414, 415, 429, 430, 431, 445, 446, 447, 461, 462, 463, 477, 478, 89, 90, 91, 92, 0, 1, 2], [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 3, 4, 5, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 6, 7, 8], [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 9, 10, 11, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 12, 16, 17], [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 18, 19, 20, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 21, 22, 23], [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 24, 25, 26, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 27, 28, 32], [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 33, 34, 35, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 36, 37, 38], [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 39, 40, 41, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 42, 43, 44], [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 48, 49, 50, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 51, 52, 53], [320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 54, 55, 56, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 57, 58, 59], [352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 60, 64, 65, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 66, 67, 68], [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 69, 70, 71, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 72, 73, 74], [416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 75, 76, 80, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 81, 82, 83], [448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 84, 85, 86, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 87, 88]]
def inverseBlocks : List (List Nat) := [[93, 94, 95, 109, 110, 111, 125, 126, 127, 141, 142, 143, 157, 0, 1, 2, 158, 159, 173, 174, 175, 189, 190, 191, 205, 206, 207, 221, 222, 3, 4, 5], [223, 237, 238, 239, 253, 254, 255, 269, 270, 271, 285, 286, 287, 6, 7, 8, 301, 302, 303, 317, 318, 319, 333, 334, 335, 349, 350, 351, 365, 9, 10, 11], [366, 367, 381, 382, 383, 397, 398, 399, 413, 414, 415, 429, 430, 12, 13, 14, 431, 445, 446, 447, 461, 462, 463, 477, 478, 89, 90, 91, 92, 15, 16, 17], [96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 18, 19, 20, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 21, 22, 23], [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 24, 25, 26, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 27, 28, 29], [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 30, 31, 32, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 33, 34, 35], [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 36, 37, 38, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 39, 40, 41], [224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 42, 43, 44, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 45, 46, 47], [256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 48, 49, 50, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 51, 52, 53], [288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 54, 55, 56, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 57, 58, 59], [320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 60, 61, 62, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 63, 64, 65], [352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 66, 67, 68, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 69, 70, 71], [384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 72, 73, 74, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 75, 76, 77], [416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 78, 79, 80, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 81, 82, 83], [448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 84, 85, 86, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 87, 88]]
def inactiveBlocks : List (List Bool) := [[true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true], [true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true, false, true, true, true, true, true, true, true, true, true, true, false, false, true, true, true], [false, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true], [true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true], [true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true], [true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, false, true, false, true, false, true, false, false, true, false, false, true, true, true, true, true]]
def forward (j : Nat) : Nat :=
  if j<479 then (forwardBlocks.getD (j/32) []).getD (j%32) 0 else j
def backward (j : Nat) : Nat :=
  if j<479 then (inverseBlocks.getD (j/32) []).getD (j%32) 0 else j
def isInactive (j : Fin 1024) : Bool :=
  (inactiveBlocks.getD (j.val/32) []).getD (j.val%32) false

theorem small_certificate : ∀ b : Fin 15, ∀ o : Fin 32,
    let j := 32*b.val+o.val
    j<479 → forward j<479 ∧ backward j<479 ∧
      backward (forward j)=j ∧ forward (backward j)=j := by decide

theorem small_facts (j : Nat) (hj : j<479) :
    forward j<479 ∧ backward j<479 ∧
      backward (forward j)=j ∧ forward (backward j)=j := by
  have h := small_certificate ⟨j/32,by omega⟩ ⟨j%32,by omega⟩
  have he : 32*(j/32)+j%32=j := by omega
  dsimp only at h
  rw [he] at h
  exact h hj

theorem forward_bounds (j : Fin 1024) : forward j.val<1024 := by
  by_cases h : j.val<479
  · have := (small_facts j.val h).1; omega
  · simpa [forward,h] using j.isLt
theorem backward_bounds (j : Fin 1024) : backward j.val<1024 := by
  by_cases h : j.val<479
  · have := (small_facts j.val h).2.1; omega
  · simpa [backward,h] using j.isLt
theorem backward_forward (j : Nat) : backward (forward j)=j := by
  by_cases h : j<479
  · exact (small_facts j h).2.2.1
  · simp [forward,backward,h]
theorem forward_backward (j : Nat) : forward (backward j)=j := by
  by_cases h : j<479
  · exact (small_facts j h).2.2.2
  · simp [forward,backward,h]

def order : Fin 1024 ≃ Fin 1024 where
  toFun j := ⟨forward j.val,forward_bounds j⟩
  invFun j := ⟨backward j.val,backward_bounds j⟩
  left_inv j := Fin.ext (backward_forward j.val)
  right_inv j := Fin.ext (forward_backward j.val)
def inactive : Finset (Fin 1024) := Finset.univ.filter (fun j => isInactive j)
theorem pivot_fixed : order (1023 : Fin 1024)=1023 := by decide
theorem pivot_inactive : (1023 : Fin 1024) ∈ inactive := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by decide⟩
theorem residual_order_agrees (i : Fin 111) :
    (order ⟨i.val,by omega⟩).val=ResidualPins.order i := by
  revert i; decide
theorem residual_inactive_agrees (i : Fin 111) :
    isInactive (order ⟨i.val,by omega⟩)=ResidualPins.inactive i := by
  revert i; decide

#print axioms small_certificate
#print axioms small_facts
#print axioms forward_bounds
#print axioms backward_bounds
#print axioms backward_forward
#print axioms forward_backward
#print axioms pivot_fixed
#print axioms pivot_inactive
#print axioms residual_order_agrees
#print axioms residual_inactive_agrees
end AspisR19.T163SourceTable
