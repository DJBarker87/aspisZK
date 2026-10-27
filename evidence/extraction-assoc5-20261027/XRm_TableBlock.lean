import XRm_GeometryPoint
open Aeneas Aeneas.Std Result
open XRk_Release XRm_FieldCanonical
namespace XRm_TableBlock
def Good (p : U32 × U32) : Prop := M p.1 ∧ M p.2
def All (xs : List (U32 × U32)) : Prop := ∀ p ∈ xs, Good p
theorem append (xs ys : List (U32 × U32)) (hx : All xs) (hy : All ys) : All (xs++ys) := by
  intro p h
  rcases List.mem_append.mp h with h|h
  · exact hx p h
  · exact hy p h
theorem first : All [(1022251061#u32,788094511#u32),(788094511#u32,1125232586#u32),(1462922215#u32,117240331#u32),(117240331#u32,684561432#u32),(479936188#u32,217587789#u32),(217587789#u32,1667547459#u32),(797223315#u32,1892184156#u32),(1892184156#u32,1350260332#u32),(1601663285#u32,2022005567#u32),(2022005567#u32,545820362#u32),(1715132412#u32,1963268365#u32),(1963268365#u32,432351235#u32),(1329069890#u32,1640136239#u32),(1640136239#u32,818413757#u32),(1052324090#u32,1064735370#u32),(1064735370#u32,1095159557#u32),(119109612#u32,1742172267#u32),(1742172267#u32,2028374035#u32),(1949036272#u32,2084561085#u32),(2084561085#u32,198447375#u32),(1276985988#u32,456990464#u32),(456990464#u32,870497659#u32),(818046810#u32,1849544479#u32),(1849544479#u32,1329436837#u32),(1068288753#u32,675427495#u32),(675427495#u32,1079194894#u32),(2144102382#u32,886761621#u32),(886761621#u32,3381265#u32),(1542630618#u32,1177056098#u32),(1177056098#u32,604853029#u32),(270443035#u32,1665395253#u32),(1665395253#u32,1877040612#u32)] := by
  intro p h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31
  all_goals subst p; constructor <;> scalar_tac
#print axioms first
#print axioms append
end XRm_TableBlock
