"""Exact conditional native-IO success of the source reservation, without a client-success premise."""
from pathlib import Path
import json
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-reach-20261027/resume10';steps=json.load(open(E/'store-prefix-plan.json'))['steps']
base='aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore'
args=' (store : Store) (statement nonce : Array U8 32#usize)';applyargs='store statement nonce';proof='  unfold '+base+'.reserve_fallible\n'
for j,(v,t,c) in enumerate(steps):
 if j not in [9,11]:args+=f'\n    ({v} : {t})';applyargs+=' '+v
 res=f'.Ok {v}' if j==5 else f'(.Ok (),{v})' if j in [6,7,8] else '.Ok ()' if j in [9,11] else v
 args+=f' (h{j} : {c} = .ok ({res}))';applyargs+=' h'+str(j)
 proof+=f'  change ({c} >>= _) = _\n  rw [h{j}]\n'
text='''import R1Z.PV_RE_StorePrefix1011
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_StoreSuccess10
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Store := aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore
'''
text+='theorem fallible'+args+f''' :
    {base}.reserve_fallible store statement nonce =
      .ok (.Ok true,{{store with last_error := none}}) := by
'''+proof+'  rfl\n#print axioms fallible\n'
text+='theorem reserved'+args+f''' :
    {base}.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve store statement nonce =
      .ok (true,{{store with last_error := none}}) := by
  unfold {base}.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore.reserve
  rw [fallible {applyargs}]
  rfl
#print axioms reserved
end R1Z.PV_RE_StoreSuccess10
'''
(L/'PV_RE_StoreSuccess10.lean').write_text(text)
