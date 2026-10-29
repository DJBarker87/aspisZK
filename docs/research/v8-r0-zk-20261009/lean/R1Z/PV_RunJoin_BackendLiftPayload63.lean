import R1Z.PV_RunJoin_BackendLiftRows63
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BackendLiftPayload63
open Aeneas Aeneas.Std ProverRwFull
open PV_RunJoin_BackendMRows58
abbrev W := aspis_core.field.wide_exact.WideExact

def rows (v : Nat → W) (start : Nat) : Nat → List W
  | 0 => []
  | n+1 => v start::rows v (start+1) n

theorem complete (columns : Columns) (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (l start n : Nat) (hl : l<26) (bound : start+n≤1024) :
    PV_RunJoin_LiftValue63.widePayload (column columns l) start n=
      rows (values columns hlen l) start n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [PV_RunJoin_LiftValue63.widePayload,rows]
    rw [PV_RunJoin_BackendLiftRows63.entry columns hlen l start hl (by omega),
      ih (start+1) (by omega)]
    rfl

theorem source_image (columns : Columns) (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (l start n : Nat) (hl : l<26) (bound : start+n≤1024) :
    (PV_RunJoin_LiftPayload63.payload (column columns l) start n).map PV_RunJoin_LiftValue63.value=
      rows (values columns hlen l) start n := by
  rw [PV_RunJoin_LiftValue63.map_payload,complete columns hlen l start n hl bound]

#print axioms rows
#print axioms complete
#print axioms source_image
end R1Z.PV_RunJoin_BackendLiftPayload63
