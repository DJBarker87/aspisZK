import R1Z.PV_RunJoin_PolyPayloadWindow72
import R1Z.PV_RunJoin_PolyCellCanonical72
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PolyPayloadCanonicalWindow73
open Aeneas Aeneas.Std ProverRwFull PV_RunJoin_PolyCell38 PV_RunJoin_PolyLoop38

variable [ExternalTypes]

theorem complete (p : Nat → Q) (start n i : Nat) (bound : i<n) :
    ∃ w : aspis_core.field.wide_exact.WideExact,
      ((payload p start n).drop (32*i)).take 32=(PV_RunJoin_FlatBytes35.wire w).val ∧
      PV_RunJoin_WideLimbsParse72.Canonical w ∧
      w.c1=⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩ := by
  exact ⟨wide (p (start+i)),PV_RunJoin_PolyPayloadWindow72.complete p start n i bound,
    PV_RunJoin_PolyCellCanonical72.complete _,rfl⟩

#print axioms complete
end R1Z.PV_RunJoin_PolyPayloadCanonicalWindow73
