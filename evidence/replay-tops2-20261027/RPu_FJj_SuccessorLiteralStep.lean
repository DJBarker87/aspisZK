import RPu_FJj_SuccessorModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_SuccessorLiteralStep
variable {K : Type} [Field K]

def state (z : Fin 10 → K) (e : Nat) : K × (Fin 10 → K) :=
  (R0P.SemSource.succCarry z (10-e),fun j=>if e≤j.val then R0P.SemSource.successorPoint z j else z j)

theorem carry (z : Fin 10 → K) (e : Nat) (he : e<10) :
    z ⟨e,he⟩*R0P.SemSource.succCarry z (10-(e+1))=R0P.SemSource.succCarry z (10-e) := by
  have en : 10-e=(9-e)+1 := by omega
  have ci : 9-(9-e)=e := by omega
  rw [en,R0P.SemSource.succCarry]
  simp only [dif_pos (show 9-e<10 by omega)]
  have eq : (⟨9-(9-e),by omega⟩ : Fin 10)=⟨e,he⟩ := Fin.ext ci
  rw [eq]
  have ce : 10-(e+1)=9-e := by omega
  rw [ce]

theorem value (z : Fin 10 → K) (e : Nat) (he : e<10) :
    FJd_LoopReference.successorStep z (state z (e+1)) (FJj_SuccessorModel.index e)=state z e := by
  have idx : FJj_SuccessorModel.index e=⟨e,he⟩ := by apply Fin.ext;exact Nat.mod_eq_of_lt he
  rw [idx]
  apply Prod.ext
  · exact carry z e he
  · funext j
    unfold FJd_LoopReference.successorStep state
    change Function.update (fun j : Fin 10=>if e+1≤j.val then R0P.SemSource.successorPoint z j else z j)
      ⟨e,he⟩ (z ⟨e,he⟩+R0P.SemSource.succCarry z (10-(e+1))-
        (z ⟨e,he⟩*R0P.SemSource.succCarry z (10-(e+1))+
          z ⟨e,he⟩*R0P.SemSource.succCarry z (10-(e+1)))) j=
      (if e≤j.val then R0P.SemSource.successorPoint z j else z j)
    by_cases hj : j=⟨e,he⟩
    · subst j
      rw [Function.update_self,if_pos (Nat.le_refl e)]
      unfold R0P.SemSource.successorPoint
      have ce : 10-(e+1)=9-e := by omega
      rw [ce]
    · rw [Function.update_of_ne hj]
      have jn : j.val≠e := by intro h;apply hj;exact Fin.ext h
      have eq : (e+1≤j.val) ↔ (e≤j.val) := by omega
      simp only [eq]
#print axioms carry
#print axioms value
end AspisR1.FJj_SuccessorLiteralStep
end
