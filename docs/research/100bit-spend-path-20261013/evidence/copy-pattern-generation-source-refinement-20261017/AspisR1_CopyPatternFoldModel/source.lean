import R0P.Copy

/-! Symbolic traversal equations for the retained sixteen-lane pattern fold. -/
set_option autoImplicit false
namespace AspisR1.CopyPatternFoldModel
variable {K : Type} [Field K]

def lanes : List (Fin 16) := List.ofFn (fun i : Fin 16 => i)

def step (pattern : R0P.CopyPattern) (openings powers : Fin 16 → K)
    (value : K) (limb : Fin 16) : K :=
  if pattern.kinds limb = 1 then
    value + powers limb * (openings (pattern.columns limb) + (pattern.offsets limb : K))
  else value

def remaining (pattern : R0P.CopyPattern) (openings powers : Fin 16 → K)
    (cursor : Nat) (value : K) : K :=
  (lanes.drop cursor).foldl (step pattern openings powers) value

theorem lanes_length : lanes.length = 16 := by simp [lanes]

theorem lanes_getElem (i : Fin 16) : lanes[i.val]'(by rw [lanes_length]; exact i.isLt) = i := by
  simp only [lanes, List.getElem_ofFn]

theorem remaining_end (pattern : R0P.CopyPattern) (openings powers : Fin 16 → K)
    (value : K) : remaining pattern openings powers 16 value = value := by
  unfold remaining
  have hdrop : lanes.drop 16 = [] := List.drop_eq_nil_iff.mpr (by rw [lanes_length])
  rw [hdrop]
  rfl

theorem remaining_step (pattern : R0P.CopyPattern) (openings powers : Fin 16 → K)
    (cursor : Fin 16) (value : K) :
    remaining pattern openings powers cursor.val value =
      remaining pattern openings powers (cursor.val + 1)
        (step pattern openings powers value cursor) := by
  unfold remaining
  have hi : cursor.val < lanes.length := by rw [lanes_length]; exact cursor.isLt
  rw [List.drop_eq_getElem_cons hi, lanes_getElem cursor]
  rfl

theorem remaining_zero (openings : Fin 16 → K) (lambda : K) (index : Fin 14) :
    remaining (R0P.copyPatterns index) openings (R0P.copyPowers lambda) 0 0 =
      R0P.copyPatternValuesLiteral openings lambda index := by rfl

#print axioms lanes_length
#print axioms lanes_getElem
#print axioms remaining_end
#print axioms remaining_step
#print axioms remaining_zero
end AspisR1.CopyPatternFoldModel
