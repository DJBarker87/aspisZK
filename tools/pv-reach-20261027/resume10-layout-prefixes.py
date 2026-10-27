"""Keep material sampling in source order without evaluating recurrences."""
from pathlib import Path
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
f='aspis_prover.state_only_hiding.'
steps=[
 ('store1','S','inst.reserve store context.statement_digest context.mask_nonce','.ok (true,store1)'),
 ('seed','Array U8 32#usize',f+'derive_state_only_mask_seed_from_entropy_ref hash binding context entropy','.ok (.Ok seed)'),
 ('expander','Expander',f+'SeedExpander.new hash seed','.ok expander'),
 ('inactive','Usize',f+'first_inactive_row active','.ok inactive'),
 ('c1','alloc.vec.Vec aspis_core.field.M31',f+'sample_mask_cells expander (Slice.len cells)','.ok (.Ok c1,expander1)'),
 ('columns','Array (alloc.vec.Vec aspis_core.field.M31) 10#usize',f+'sample_mask_columns expander1 inactive active','.ok (.Ok columns,expander2)'),
 ('g','alloc.vec.Vec aspis_core.field.QM31',f+'sample_mask_g expander2 inactive active','.ok (.Ok g,expander3)'),
 ('h1','alloc.vec.Vec aspis_core.field.QM31',f+'sample_mask_h1_padding expander3 inactive active','.ok (.Ok h1,expander4)')]
for i,(_,_,call,_) in enumerate(steps):
 ns=f'PV_RE_LayoutPrefix10{i:02d}'
 head=f'''import R1Z.PV_RE_BindTransport10
set_option autoImplicit false
noncomputable section
namespace R1Z.{ns}
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Context := aspis_core.state_only_hiding.StateOnlyHidingContext
abbrev Expander := aspis_prover.state_only_hiding.SeedExpander
abbrev Hash := Slice (Slice U8) → Result (Array U8 32#usize)
'''
 args=''' {S : Type} (inst : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (hash : Hash) (binding : Array U8 32#usize) (context : Context)
    (entropy : Array U8 32#usize) (store : S)
    (cells : Slice aspis_statement.trace_v4.TraceCell) (active : Array Bool 1024#usize)'''
 proof='  unfold '+f+'build_mask_material_for_layout\n'
 for j,(v,t,c,res) in enumerate(steps[:i]):
  args+=f'\n    ({v} : {t})'
  if j>=4:args+=f' (expander{j-3} : Expander)'
  args+=f' (h{j} : {c} = {res})'
  proof+=f'  change ∃ next, ({c} >>= _) = _\n  rw [h{j}]\n'
 proof+='  exact ⟨_,rfl⟩\n'
 text=head+f'''theorem prefix{args} :
    ∃ next, {f}build_mask_material_for_layout inst hash binding context entropy store cells active =
      ({call} >>= next) := by
'''+proof+f'''#print axioms prefix
end R1Z.{ns}
'''
 (L/(ns+'.lean')).write_text(text)
