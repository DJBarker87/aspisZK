"""Mechanically change the accepted source spine's execution carrier to Prefix.
The original source parser remains retry.py; neither sourceBody nor its source
association proof is replaced. Callees retain explicit unfinished status.
"""
from pathlib import Path
import hashlib,json,sys
E=Path('evidence/pv-evh5-20261029')
s=Path('lean/PV_EVH_RetryBody.lean').read_text()
assert hashlib.sha256(s.encode()).hexdigest()==json.load(open(E/'receipt-73624.json'))['source_sha256']
s=s[s.index('/-- Only the retry source spine.'):s.index('\n#print axioms body_fixed')]
s=s.replace('Next T0','NextP T0').replace('prove_OPEN : Prove','prove_OPEN : ProveP')
s=s.replace(': M (ControlFlow',': P (ControlFlow')
s=s.replace('PV_EVH_World.lift','PV_EVH_Prefix.lift')
s=s.replace('← PV_EVH_World.attempt','← PV_EVH_Prefix.ofM PV_EVH_World.attempt')
s=s.replace('← PV_EVH_World.retry','← PV_EVH_Prefix.ofM PV_EVH_World.retry')
s=s.replace('FixedView','FinishedView').replace('fixed_bind','PV_EVH_Prefix.bind_fixed').replace('fixed_lift','PV_EVH_Prefix.lift_fixed')
s=s.replace('intro w; rfl','intro w r h; cases h; rfl')
s=s.replace('''intro w
            exact prove_fixed _ _ _''','''apply PV_EVH_Prefix.bind_fixed (r := .ok ())
              (f := fun _ => prover.prove_masked_attempt public1 compiled variant hash val nonce_store)
            · exact PV_EVH_Prefix.ofM_fixed _ _ (fun _ => rfl)
            · intro unused
              exact prove_fixed _ _''')
out='''import PV_EVH_Prefix
import PV_EVH_RetryBody
set_option autoImplicit false
noncomputable section
namespace PV_EVH_PrefixRetryBody
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_RetryBody (Store Secrets Outcome AttemptOutcome State sourceBody)
open PV_EVH_Prefix (P FinishedView)
variable [ExternalTypes] [ExternalFuns]
abbrev NextP (T : Type) := T → Usize → P ((core.result.Result Secrets verifier.Error) × T)
abbrev ProveP := Secrets → Store → P AttemptOutcome

'''+s+'''\n
#print axioms body_fixed
end PV_EVH_PrefixRetryBody
'''
p=Path('lean/PV_EVH_PrefixRetryBody.lean')
record=json.dumps(dict(input='lean/PV_EVH_RetryBody.lean',input_sha256=hashlib.sha256(Path('lean/PV_EVH_RetryBody.lean').read_bytes()).hexdigest(),output_sha256=hashlib.sha256(out.encode()).hexdigest(),scope='Same sourceBody; compositional Prefix callee results, no completed entry claim'),indent=2)+'\n'
if '--check' in sys.argv:
 assert p.read_text()==out
 assert (E/'prefix-retry-generation.json').read_text()==record
 print('PASS prefix retry byte identity')
else:
 p.write_text(out)
 (E/'prefix-retry-generation.json').write_text(record)
