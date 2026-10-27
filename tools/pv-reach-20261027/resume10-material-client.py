"""Cross the complete client prefix into the first actual material callback."""
from pathlib import Path
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=(L/'PV_RE_ClientAfter1002.lean').read_text();head=s.split('theorem entered',1)[0].replace('PV_RE_ClientAfter1002','PV_RE_ClientMaterial10');head='import R1Z.PV_RE_ClientAfter1002\nimport R1Z.PV_RE_MaterialCells10\n'+head[head.index('set_option'):]
args=s.split('theorem entered',1)[1].split(' :\n    letI',1)[0];body=s.split('    letI : ExternalFuns := ProverRwOuterMapErr.selected ops\n',1)[1].split(' := by',1)[0];extra=body[6:body.index(',\n    ∃ next')]
whole=body.split('∃ next,',1)[1].split(' = (',1)[0].strip()
inst='aspis_prover.state_only_entropy.PreReservedNonce.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore'
text=head+'theorem entered'+args+''' :
    letI : ExternalFuns := ProverRwOuterMapErr.selected ops
    ∀ '''+extra+''',
    ∃ next, '''+whole+''' =
      (aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1 >>= next) := by
  letI : ExternalFuns := ProverRwOuterMapErr.selected ops
  intro store1 h0 entropy h1
  apply PV_RE_BindTransportB10.compose _ _ _
    (PV_RE_ClientAfter1002.entered ops entropy pub compiled hash store state state1 secret
      entropy_prefix bytes digest serialization first_hash second_hash store1 h0 entropy h1)
  exact PV_RE_MaterialCells10.entered ops '''+inst+''' hash binding digest secret.mask_nonce entropy
    {statement_digest := digest,mask_nonce := secret.mask_nonce,consumed := false}
#print axioms entered
end R1Z.PV_RE_ClientMaterial10
'''
# Raw entropy provider and returned private entropy array need different names.
text=text.replace('(entropy : Array U8 32#usize)','(private_entropy : Array U8 32#usize)').replace('.ok entropy)', '.ok private_entropy)')
text=text.replace('intro store1 h0 entropy h1','intro store1 h0 private_entropy h1').replace('store1 h0 entropy h1)','store1 h0 private_entropy h1)').replace('secret.mask_nonce entropy\n','secret.mask_nonce private_entropy\n')
(L/'PV_RE_ClientMaterial10.lean').write_text(text)
