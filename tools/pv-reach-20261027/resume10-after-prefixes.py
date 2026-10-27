"""Source-derived post-reservation prefixes; all conditions remain explicit."""
from pathlib import Path
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
head='''import R1Z.PV_RE_BindTransport10
import R1Z.ProverRwOuterAfterChecks
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_AfterPrefix10{idx:02d}
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Context := aspis_core.state_only_hiding.StateOnlyHidingContext
abbrev Secrets := aspis_prover.state_only_entropy.StateOnlyAttemptSecrets
abbrev Material := aspis_prover.state_only_hiding.StateOnlyMaskMaterial
abbrev Pre := aspis_prover.state_only_entropy.PreReservedNonce
abbrev Hash := Slice (Slice U8) → Result (Array U8 32#usize)
abbrev Z := Array.Insts.ZeroizeZeroize 32#usize (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)
'''
steps=[
 ('store1','S','inst.reserve store context.statement_digest context.mask_nonce','.ok (true,store1)'),
 ('entropy','Array U8 32#usize','zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Z secret.field_mask_entropy','.ok entropy'),
 ('material','Material','aspis_prover.state_only_hiding.build_pool_v1_pair_forest_mask_material_v1_from_entropy_ref aspis_prover.state_only_entropy.PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore hash binding context entropy ({statement_digest := context.statement_digest,mask_nonce := context.mask_nonce,consumed := false} : Pre)','.ok (.Ok material,({statement_digest := context.statement_digest,mask_nonce := context.mask_nonce,consumed := true} : Pre))'),
 ('encoded','Array U8 81#usize','aspis_core.state_only_hiding.StateOnlyHidingContext.encode context','.ok encoded'),
 ('borrowed','Slice U8','zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref (Array.Insts.CoreConvertAsRefSlice U8 32#usize) Z secret.field_mask_entropy','.ok borrowed'),
 ('seed','Array U8 32#usize','hash (Array.to_slice (Array.make 4#usize [aspis_prover.state_only_entropy.POOL_V1_SOURCE_SEED_DOMAIN,Array.to_slice binding,Array.to_slice encoded,borrowed]))','.ok seed'),
 ('wrapped','zeroize.Zeroizing (Array U8 32#usize)','zeroize.Zeroizing.new Z seed','.ok wrapped'),
 ('cleared','zeroize.Zeroizing (Array U8 32#usize)','zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize Z secret.field_mask_entropy','.ok cleared')]
for i,(_,_,call,_) in enumerate(steps):
 args=''' {S : Type} (inst : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (secret : Secrets) (hash : Hash) (binding : Array U8 32#usize)
    (context : Context) (store : S)'''
 proof='  unfold ProverRwOuterAfterChecks.afterChecks\n'
 for j,(v,t,c,res) in enumerate(steps[:i]):
  args+=f'\n    ({v} : {t}) (h{j} : {c} = {res})'
  proof+=f'  change ∃ next, ({c} >>= _) = _\n  rw [h{j}]\n'
 proof+='  exact ⟨_,rfl⟩\n'
 txt=head.format(idx=i)+'theorem prefix'+args+f''' :
    ∃ next, ProverRwOuterAfterChecks.afterChecks inst secret hash binding context store =
      ({call} >>= next) := by
'''+proof+f'''#print axioms prefix
end R1Z.PV_RE_AfterPrefix10{i:02d}
'''
 (L/f'PV_RE_AfterPrefix10{i:02d}.lean').write_text(txt)
