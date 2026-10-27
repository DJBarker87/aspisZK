import RPz7_F3K_CheckpointPreparedFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_CheckpointQueryNumeric
open Aeneas Aeneas.Std

theorem exact_queries (p : AspisR1Stage2.verifier.Prepared) (q : Fin 22 → Fin 262144)
    (coords : ∀ j : Fin 22,(p.queries.val[j.val]'(by have len : p.queries.val.length=22 := p.queries.property; omega)).val=(q j).val) :
    CheckpointBytes5Output.queries p=q := by
  funext j
  apply Fin.ext
  have hj : j.val < p.queries.val.length := by have len : p.queries.val.length=22 := p.queries.property; omega
  simp only [CheckpointBytes5Output.queries,List.getElem?_map,List.getElem?_eq_getElem hj,
    Option.map_some,Option.getD_some,coords,Nat.mod_eq_of_lt (q j).isLt]

#print axioms exact_queries
end AspisR1.F3K_CheckpointQueryNumeric
end
