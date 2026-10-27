"""Continue the original caller through the second hash into material reserve."""
from pathlib import Path
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=(L/'PV_RE_AttemptBindingHash7.lean').read_text();header=s[s.index('theorem attempt_to_bindinghash'):s.index(' :\n    ∃ next,')].replace('theorem attempt_to_bindinghash','theorem attempt_to_reserve')
proof=s[s.index('  letI : ExternalFuns := D'):s.index('  exact ⟨_,rfl⟩')]
call='''@aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1
        _ D Store
        aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore
        secret hash binding context store'''
prefix='''import R1Z.PV_RE_AttemptBindingHash7
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_AttemptReserve7
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep PV_RE_AttemptHashPrefix6 PV_RE_AttemptContext7 PV_RE_AttemptBindingHash7
variable [ExternalTypes]
'''
extra='''
    (binding : Array U8 32#usize)
    (second_hash : hash (bindingFrame bytes tag encoded) = .ok binding)'''
text=prefix+header+extra+' :\n    ∃ next, @prover.prove_masked_attempt _ D pub compiled variant hash secret store =\n      ('+call+' >>= next) := by\n'+proof+'''  change ∃ next, (hash (bindingFrame bytes tag encoded) >>= _) = _
  rw [second_hash]
  unfold prover.prove_masked_with_attempt
  exact ⟨_,rfl⟩
#print axioms attempt_to_reserve
end R1Z.PV_RE_AttemptReserve7
'''
(L/'PV_RE_AttemptReserve7.lean').write_text(text)
s=(L/'PV_RE_ClientBindingHash7.lean').read_text();header=s[s.index('theorem client_to_bindinghash'):s.index(' :\n    ∃ next,')].replace('theorem client_to_bindinghash','theorem client_to_reserve')
prefix='''import R1Z.PV_RE_AttemptReserve7
import R1Z.PV_RE_ClientBindingHash7
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_ClientReserve7
open Aeneas Aeneas.Std Result ProverRwFull PV_RE_RetryStep PV_RE_AttemptHashPrefix6 PV_RE_AttemptContext7 PV_RE_PublicPrefix6 PV_RE_AttemptBindingHash7
variable [ExternalTypes]
'''
args='D entropy pub compiled hash store state state1 secret guard entropy_prefix'
attemptargs='D pub compiled .S2 hash secret store bytes digest serialization map_error first_hash context context_prefix tag tag_prefix encoded encode_prefix binding second_hash'
text=prefix+header+extra+' :\n    ∃ next, @RealR1_client.prove_for_proof_accounts _ D C entropy pub compiled hash store state =\n      ('+call+' >>= next) := by\n  apply PV_RE_ClientAttempt7.lift_prefix '+args+'\n  exact PV_RE_AttemptReserve7.attempt_to_reserve '+attemptargs+'\n#print axioms client_to_reserve\nend R1Z.PV_RE_ClientReserve7\n'
# Explicit call argument to lift_prefix makes the higher-order boundary clear.
text=text.replace('guard entropy_prefix\n  exact', 'guard entropy_prefix ('+call+')\n  exact')
(L/'PV_RE_ClientReserve7.lean').write_text(text)
