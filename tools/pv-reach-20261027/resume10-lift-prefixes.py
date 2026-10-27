"""Generate client continuations of the exact native effects, then fail/div cases."""
from pathlib import Path
import re
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
base='aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore'
baseText=(L/'PV_RE_ReserveGuards9.lean').read_text()
clientArgs=baseText.split('theorem client_to_store',1)[1].split(' :\n    ∃ next',1)[0]
clientApp='ops entropy pub compiled hash store state state1 secret entropy_prefix bytes digest serialization first_hash second_hash'
clientWhole='@RealR1_client.prove_for_proof_accounts _ (ProverRwOuterMapErr.selected ops) C entropy pub compiled hash store state'
header='''set_option autoImplicit false
noncomputable section
namespace R1Z.{namespace}
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RE_RetryStep PV_RE_PublicPrefix6 PV_RE_AttemptHashPrefix6 PV_RE_AttemptBindingHash7
variable [ExternalTypes]
'''
for i in range(12):
 source=(L/f'PV_RE_StorePrefix10{i:02d}.lean').read_text()
 args=source.split('theorem prefix',1)[1].split(' :\n    ∃ next',1)[0]
 extra=args.split('(statement nonce : Array U8 32#usize)',1)[1]
 extra=extra.replace('statement','digest').replace('nonce','secret.mask_nonce')
 # Type expressions and functions see the selected dictionary through a local instance.
 used=[x for x in re.findall(r'\((\w+) :',extra) if not x.startswith('h')]
 ordered=[]
 for j in range(i):
  if j not in [9,11]:ordered.append(['path','options','written','created','moded','file','file1','file2','file3','synced','directory','dirsync'][j])
  ordered.append('h'+str(j))
 target=source.split(' =\n      (',1)[1].split(' >>= next)',1)[0].replace('statement','digest').replace('nonce','secret.mask_nonce')
 name=f'PV_RE_ClientStore10{i:02d}'
 # selected local dictionary must scope every IO-prefix assumption and target.
 argsAll=clientArgs+ '\n    '+extra.strip()
 declaration=f'''theorem prefix{clientArgs} :
    letI : ExternalFuns := ProverRwOuterMapErr.selected ops
    ∀ {extra.strip()},
    ∃ next, {clientWhole} = ({target} >>= next) := by
  letI : ExternalFuns := ProverRwOuterMapErr.selected ops
'''
 if not extra.strip():declaration=declaration.replace('    ∀ ,\n','')
 # The extra binders are already parenthesized; ∀ (x : T) (h : ...) syntax requires comma, okay.
 intro=' '.join(ordered)
 if intro:declaration+='  intro '+intro+'\n'
 declaration+=f'''  obtain ⟨next,hn⟩ := PV_RE_ReserveGuards9.client_to_store {clientApp}
  unfold {base}.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve at hn
  rw [PV_RE_ClientEntry.bind_assoc] at hn
  obtain ⟨tail,ht⟩ := PV_RE_StorePrefix10{i:02d}.prefix store digest secret.mask_nonce {' '.join(ordered)}
  rw [ht,PV_RE_ClientEntry.bind_assoc] at hn
  exact ⟨_,hn⟩
#print axioms prefix
'''
 text=f'import R1Z.PV_RE_StorePrefix10{i:02d}\nimport R1Z.PV_RE_ReserveGuards9\n'+header.format(namespace=name)+declaration+f'end R1Z.{name}\n'
 (L/(name+'.lean')).write_text(text)
for i in range(8):
 source=(L/f'PV_RE_AfterPrefix10{i:02d}.lean').read_text()
 extra=source.split('theorem prefix',1)[1].split(' :\n    ∃ next',1)[0].split('(store : S)',1)[1]
 context='(ProverRwOuterContextModel.context digest secret.mask_nonce)'
 inst=base+'.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore'
 extra=re.sub(r'\bS\b','Store',extra);extra=re.sub(r'\bcontext\b',context,extra);extra=re.sub(r'\binst\.reserve\b',inst+'.reserve',extra)
 # The source prefix abbreviations are imported and kept qualified through open.
 target=source.split(' =\n      (',1)[1].split(' >>= next)',1)[0]
 target=re.sub(r'\bcontext\b',context,target);target=re.sub(r'\binst\.reserve\b',inst+'.reserve',target)
 ordered=[]
 for j in range(i):ordered += [['store1','entropy','material','encoded','borrowed','seed','wrapped','cleared'][j],f'h{j}']
 name=f'PV_RE_ClientAfter10{i:02d}'
 declaration=f'''theorem prefix{clientArgs} :
    letI : ExternalFuns := ProverRwOuterMapErr.selected ops
    ∀ {extra.strip()},
    ∃ next, {clientWhole} = ({target} >>= next) := by
  letI : ExternalFuns := ProverRwOuterMapErr.selected ops
'''
 if not extra.strip():declaration=declaration.replace('    ∀ ,\n','')
 if ordered:declaration+='  intro '+' '.join(ordered)+'\n'
 declaration+=f'''  apply PV_RE_BindTransport10.compose _ _ _
    (PV_RE_AfterChecks10.client_to_afterChecks {clientApp})
  exact PV_RE_AfterPrefix10{i:02d}.prefix {inst} secret hash binding {context} store {' '.join(ordered)}
#print axioms prefix
'''
 text=f'import R1Z.PV_RE_AfterPrefix10{i:02d}\nimport R1Z.PV_RE_AfterChecks10\n'+header.format(namespace=name)+f'open PV_RE_AfterPrefix10{i:02d}\n'+declaration+f'end R1Z.{name}\n'
 (L/(name+'.lean')).write_text(text)
