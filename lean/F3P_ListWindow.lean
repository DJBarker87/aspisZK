import F3P_SliceIndex
set_option autoImplicit false
namespace AspisR1.F3P_ListWindow

theorem window {A : Type} (s : List A) (start n : Nat) (v : Fin n → A)
    (read : ∀ j : Fin n,s[start+j.val]?=some (v j)) :
    (s.drop start).take n=List.ofFn v := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i<n
  · simp [List.getElem?_take,List.getElem?_drop,hi,read ⟨i,hi⟩]
  · simp [List.getElem?_take,List.getElem?_drop,hi]


#print axioms window
end AspisR1.F3P_ListWindow
