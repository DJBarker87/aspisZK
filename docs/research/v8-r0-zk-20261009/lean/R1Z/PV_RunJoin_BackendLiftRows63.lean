import R1Z.PV_RunJoin_LiftValue63
import R1Z.PV_RunJoin_BackendMRows58
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BackendLiftRows63
open Aeneas Aeneas.Std ProverRwFull
open PV_RunJoin_BackendMRows58

theorem entry (columns : Columns) (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (l j : Nat) (hl : l<26) (hj : j<1024) :
    PV_RunJoin_LiftPayload63.entry (column columns l) j=element columns hlen l j := by
  have bound : j<(column columns l).val.length := by
    change j<(column columns l).length
    rw [hlen l hl]
    exact hj
  simp only [PV_RunJoin_LiftPayload63.entry,element,Nat.mod_eq_of_lt hl,
    Nat.mod_eq_of_lt hj,List.getElem?_eq_getElem bound,Option.getD_some]

theorem cell (columns : Columns) (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (l j : Nat) (hl : l<26) (hj : j<1024) :
    PV_RunJoin_LiftValue63.value (PV_RunJoin_LiftCell63.lifted
      (PV_RunJoin_LiftPayload63.entry (column columns l) j))=values columns hlen l j := by
  rw [PV_RunJoin_LiftValue63.cell,entry columns hlen l j hl hj]
  rfl

#print axioms entry
#print axioms cell
end R1Z.PV_RunJoin_BackendLiftRows63
