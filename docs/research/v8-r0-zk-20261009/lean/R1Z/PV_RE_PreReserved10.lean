import R1Z.ProverRwOuterGuardLeaves
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_PreReserved10
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Pre := aspis_prover.state_only_entropy.PreReservedNonce
abbrev reserve := aspis_prover.state_only_entropy.PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve

theorem fresh (digest nonce : Array U8 32#usize) :
    reserve ({statement_digest := digest,mask_nonce := nonce,consumed := false} : Pre) digest nonce =
      .ok (true,({statement_digest := digest,mask_nonce := nonce,consumed := true} : Pre)) := by
  unfold reserve aspis_prover.state_only_entropy.PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
  simp only [ProverRwOuterGuardLeaves.array_ne_self,bind_tc_ok,Bool.false_eq_true,if_false]

theorem consumed (self : Pre) (digest nonce : Array U8 32#usize) (used : self.consumed = true) :
    reserve self digest nonce = .ok (false,self) := by
  unfold reserve aspis_prover.state_only_entropy.PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
  rw [used]
  rfl
#print axioms fresh
#print axioms consumed
end R1Z.PV_RE_PreReserved10
