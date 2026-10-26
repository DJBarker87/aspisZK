import P2P_Charge
set_option autoImplicit false
namespace AspisR1.P2P_Union
/-- Both pointwise failure routes land in one literal account event, so
unioning them needs no second collision mass. -/
theorem same_event (canonical binding charged : Prop)
    (canonicalCharge : canonical → charged) (bindingCharge : binding → charged) :
    canonical ∨ binding → charged := Or.elim · canonicalCharge bindingCharge

theorem reads_fit (Q : Nat) : Q+1921+1040+4=Q+2965 := by omega

#print axioms same_event
#print axioms reads_fit
end AspisR1.P2P_Union
