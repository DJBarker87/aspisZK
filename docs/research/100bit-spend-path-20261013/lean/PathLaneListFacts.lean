import R0P.Path

/-! Pointwise residual-list facts for the retained 1+8+8 path family. -/
set_option autoImplicit false
namespace AspisR1.PathLaneListFacts
variable {K : Type} [Field K]

theorem bit_cell (q : K) (o : R0P.Openings K) :
    (R0P.pathLanes q o)[0]'(by simp [R0P.pathLanes]) = q * (o.z 0 * (o.z 0 - 1)) := by
  simp [R0P.pathLanes]

theorem left_cell (q : K) (o : R0P.Openings K) (i : Fin 8) :
    (R0P.pathLanes q o)[1 + i.val]'(by simp [R0P.pathLanes]; omega) =
      q * (1 - o.z 0) *
        (o.succ (i.castAdd 8) - o.z (i.addNat 1 |>.castLE (by omega))) := by
  have h9 : 1 + i.val < 1 + 8 := by omega
  have hn1 : ¬ 1 + i.val < 1 := by omega
  simp only [R0P.pathLanes, List.getElem_append, List.length_append,
    List.length_cons, List.length_nil, List.length_ofFn, dif_pos h9,
    dif_neg hn1, List.getElem_ofFn]
  have hsub : 1 + i.val - 1 = i.val := by omega
  have hi : (⟨1 + i.val - 1, by omega⟩ : Fin 8) = i := Fin.ext hsub
  rw [hi]

theorem right_cell (q : K) (o : R0P.Openings K) (i : Fin 8) :
    (R0P.pathLanes q o)[9 + i.val]'(by simp [R0P.pathLanes]; omega) =
      q * o.z 0 *
        (o.succ (i.natAdd 8) - o.z (i.addNat 1 |>.castLE (by omega))) := by
  have hn9 : ¬ 9 + i.val < 1 + 8 := by omega
  have hn1 : ¬ 9 + i.val < 1 := by omega
  simp only [R0P.pathLanes, List.getElem_append, List.length_append,
    List.length_cons, List.length_nil, List.length_ofFn, dif_neg hn9,
    dif_neg hn1, List.getElem_ofFn]
  have hsub : 9 + i.val - (1 + 8) = i.val := by omega
  have hi : (⟨9 + i.val - (1 + 8), by omega⟩ : Fin 8) = i := Fin.ext hsub
  rw [hi]

#print axioms bit_cell
#print axioms left_cell
#print axioms right_cell
end AspisR1.PathLaneListFacts
