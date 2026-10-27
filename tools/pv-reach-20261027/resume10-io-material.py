"""Replace the opaque reserve-success hypothesis with every ordered native IO reply."""
from pathlib import Path
import re
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=(L/'PV_RE_ClientMaterial10.lean').read_text();header=s.split('theorem entered',1)[0].replace('PV_RE_ClientMaterial10','PV_RE_ClientIOMaterial10');header='import R1Z.PV_RE_StoreSuccess10\nimport R1Z.PV_RE_ClientMaterial10\n'+header[header.index('set_option'):]
args=s.split('theorem entered',1)[1].split(' :\n    letI',1)[0]
st=(L/'PV_RE_StoreSuccess10.lean').read_text();io=st.split('theorem fallible',1)[1].split(' :\n    aspis_prover',1)[0].split('(statement nonce : Array U8 32#usize)',1)[1];io=io.replace('statement','digest').replace('nonce','secret.mask_nonce')
ordered=[]
for j in range(12):
 if j not in [9,11]:ordered.append(['path','options','written','created','moded','file','file1','file2','file3','synced','directory','dirsync'][j])
 ordered.append('h'+str(j))
whole='@RealR1_client.prove_for_proof_accounts _ (ProverRwOuterMapErr.selected ops) C entropy pub compiled hash store state'
text=header+'theorem entered'+args+''' :
    letI : ExternalFuns := ProverRwOuterMapErr.selected ops
    ∀ '''+io.strip()+'''
    (private_entropy : Array U8 32#usize)
    (entropy_read : zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref Z secret.field_mask_entropy = .ok private_entropy),
    ∃ next, '''+whole+''' =
      (aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1 >>= next) := by
  letI : ExternalFuns := ProverRwOuterMapErr.selected ops
  intro '''+' '.join(ordered)+''' private_entropy entropy_read
  exact PV_RE_ClientMaterial10.entered ops entropy pub compiled hash store state state1 secret
    entropy_prefix bytes digest serialization first_hash second_hash
    {store with last_error := none}
    (PV_RE_StoreSuccess10.reserved store digest secret.mask_nonce '''+' '.join(ordered)+''')
    private_entropy entropy_read
#print axioms entered
end R1Z.PV_RE_ClientIOMaterial10
'''
(L/'PV_RE_ClientIOMaterial10.lean').write_text(text)
