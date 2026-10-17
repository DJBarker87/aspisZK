import R0P.Copy

set_option autoImplicit false
namespace R0P

variable {K : Type} [Field K]

private def activeBits16 : List (Fin 16) :=
  List.ofFn (fun i : Fin 16 => i)

theorem active_bits_6144 :
    activeBits16.filter (fun i => (6144 : Nat).testBit i.val) = [11, 12] := by
  decide

theorem active_bits_6145 :
    activeBits16.filter (fun i => (6145 : Nat).testBit i.val) = [0, 11, 12] := by
  decide

theorem active_bits_4097 :
    activeBits16.filter (fun i => (4097 : Nat).testBit i.val) = [0, 12] := by
  decide

theorem active_bits_2048 :
    activeBits16.filter (fun i => (2048 : Nat).testBit i.val) = [11] := by
  decide

theorem active_bits_2049 :
    activeBits16.filter (fun i => (2049 : Nat).testBit i.val) = [0, 11] := by
  decide

theorem active_bits_26214 :
    activeBits16.filter (fun i => (26214 : Nat).testBit i.val) =
      [1, 2, 5, 6, 9, 10, 13, 14] := by
  decide

theorem active_bits_1749 :
    activeBits16.filter (fun i => (1749 : Nat).testBit i.val) =
      [0, 2, 4, 6, 7, 9, 10] := by
  decide

private theorem mask_sum_of_bits (v : Fin 16 → K) (mask : Nat)
    (indices : List (Fin 16))
    (hbits : activeBits16.filter (fun i => mask.testBit i.val) = indices)
    (hsmall : indices.length ≤ 8) :
    copySelectorMaskSum16 v mask =
      indices.foldl (fun sum i => sum + v i) 0 := by
  have hbits' : (List.ofFn (fun i : Fin 16 => i)).filter
      (fun i : Fin 16 => mask.testBit i.val) = indices := by
    simpa only [activeBits16] using hbits
  have hnot : ¬ indices.length > 8 := by omega
  unfold copySelectorMaskSum16
  simp only [hbits', hnot, if_false]

theorem copy_selector_mask_sum_6144 (v : Fin 16 → K) :
    copySelectorMaskSum16 v 6144 = v 11 + v 12 := by
  have h := mask_sum_of_bits v 6144 [11, 12] active_bits_6144 (by decide)
  simpa using h

theorem copy_selector_mask_sum_6145 (v : Fin 16 → K) :
    copySelectorMaskSum16 v 6145 = v 0 + v 11 + v 12 := by
  have h := mask_sum_of_bits v 6145 [0, 11, 12] active_bits_6145 (by decide)
  simpa using h

theorem copy_selector_mask_sum_4097 (v : Fin 16 → K) :
    copySelectorMaskSum16 v 4097 = v 0 + v 12 := by
  have h := mask_sum_of_bits v 4097 [0, 12] active_bits_4097 (by decide)
  simpa using h

theorem copy_selector_mask_sum_2048 (v : Fin 16 → K) :
    copySelectorMaskSum16 v 2048 = v 11 := by
  have h := mask_sum_of_bits v 2048 [11] active_bits_2048 (by decide)
  simpa using h

theorem copy_selector_mask_sum_2049 (v : Fin 16 → K) :
    copySelectorMaskSum16 v 2049 = v 0 + v 11 := by
  have h := mask_sum_of_bits v 2049 [0, 11] active_bits_2049 (by decide)
  simpa using h

theorem copy_selector_mask_sum_26214 (v : Fin 16 → K) :
    copySelectorMaskSum16 v 26214 =
      v 1 + v 2 + v 5 + v 6 + v 9 + v 10 + v 13 + v 14 := by
  have h := mask_sum_of_bits v 26214 [1, 2, 5, 6, 9, 10, 13, 14]
    active_bits_26214 (by decide)
  simpa using h

theorem copy_selector_mask_sum_1749 (v : Fin 16 → K) :
    copySelectorMaskSum16 v 1749 =
      v 0 + v 2 + v 4 + v 6 + v 7 + v 9 + v 10 := by
  have h := mask_sum_of_bits v 1749 [0, 2, 4, 6, 7, 9, 10]
    active_bits_1749 (by decide)
  simpa using h

#print axioms copy_selector_mask_sum_6144
#print axioms copy_selector_mask_sum_6145
#print axioms copy_selector_mask_sum_4097
#print axioms copy_selector_mask_sum_2048
#print axioms copy_selector_mask_sum_2049
#print axioms copy_selector_mask_sum_26214
#print axioms copy_selector_mask_sum_1749

end R0P
