"""Full signatures, structures and axioms for the focused material/caller closure."""
from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[3];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
roots=['LastAttempt','Reservation','Preflight']
s=''.join('import R1Z.ProverRwRngMaterial'+x+'\n' for x in roots)+'set_option autoImplicit false\n'
for p in sorted(L.glob('ProverRwRngMaterial*.lean')):
 if p.stem.endswith('Audit'):continue
 for name in re.findall(r'^theorem (\w+)',p.read_text(),re.M):
  full='R1Z.'+p.stem+'.'+name
  s+='#check @'+full+'\n#print axioms '+full+'\n'
N='ProverRwRngMaterialBody.'
structs=['TypeLeaves','LocalLeaves','aspis_prover.state_only_hiding.StateOnlyMaskNonceStore',
 'aspis_prover.state_only_hiding.StateOnlyMaskMaterial','aspis_prover.state_only_hiding.SeedExpander',
 'aspis_prover.state_only_entropy.PreReservedNonce','prover.MaskedFixtureAudit','prover.RetriedProof',
 'aspis_core.state_only_hiding.StateOnlyHidingContext','aspis_prover.state_only_entropy.StateOnlyAttemptSecrets',
 'aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets','aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore',
 'aspis_prover.state_only_entropy.PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve',
 'aspis_prover.state_only_hiding.derive_state_only_mask_seed_from_entropy_ref',
 'aspis_prover.state_only_hiding.build_mask_material_for_layout',
 'aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref',
 'aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.reserve_and_build_pool_v1_pair_forest_mask_material_v1',
 'prover.prove_masked_attempt','prover.prove_masked_with_attempt','prover.retry_attempt','prover.prove_masked_retrying_with']
for name in structs:s+='#print '+N+name+'\n'
for module,names in {'Control':['LayoutOk','freshAck','usedAck','material','seedInput','derefEntropy'],
 'Invariant':['Returns','Post'], 'Reservation':['AfterReserve'],
 'Finish':['sourceSeedInput','asrefEntropy','wrapSeed','clearEntropy'],
 'Producer':['statusFor','contextFor','privateDomain','publicHashInput','bindingInput'],
 'Caller':['Policy']}.items():
 for name in names:s+='#print R1Z.ProverRwRngMaterial'+module+'.'+name+'\n'
p=L/'ProverRwRngMaterialAudit.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print('Audit includes',s.count('#print axioms'),'full signatures/axioms')
