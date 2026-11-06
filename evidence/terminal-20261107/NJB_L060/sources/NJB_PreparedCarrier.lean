import NJB_ArrayCarrier
import NJB_PreparedLaws
set_option autoImplicit false
namespace AspisR1.NJB_PreparedCarrier
open Aeneas Aeneas.Std
open FIv_PreparedNew (NP)
theorem size : (3#usize).val=3 := by scalar_tac
abbrev Index := Fin (3#usize).val
/-- Nine-word logical observation corresponding to cfg-only NJB_observe. -/
def words (p : NP) (i j : Index) : U32 :=
 NJB_ArrayCarrier.cell (NJB_ArrayCarrier.cell p.components i) j
def value (w : Index → Index → U32) : NP :=
 ⟨NJB_ArrayCarrier.array (fun i=>NJB_ArrayCarrier.array (w i))⟩
theorem words_value (w : Index → Index → U32) : words (value w)=w := by
 funext i j
 simp only [words,value,NJB_ArrayCarrier.cell_array]
theorem value_words (p : NP) : value (words p)=p := by
 have rows : (fun i=>NJB_ArrayCarrier.array (words p i))=NJB_ArrayCarrier.cell p.components := by
  funext i
  exact NJB_ArrayCarrier.array_cell _
 unfold value
 rw [rows,NJB_ArrayCarrier.array_cell]
 cases p
 rfl
theorem ext (x y : NP) (same : ∀ i j,words x i j=words y i j) : x=y := by
 rw [←value_words x,←value_words y]
 exact congrArg value (funext (fun i=>funext (same i)))
#print axioms size
#print axioms words_value
#print axioms value_words
#print axioms ext
end AspisR1.NJB_PreparedCarrier
