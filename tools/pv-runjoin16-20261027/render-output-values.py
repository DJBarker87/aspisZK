"""Named init/absorb equations compose three checked rounds for each output note."""
from pathlib import Path
import json,hashlib,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin16-20261027';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s='''import R1Z.PV_RunJoin_OutputRecipient16
import R1Z.PV_RunJoin_OutputTransferChange16
import R1Z.PV_RunJoin_OutputWithdrawalChange16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_OutputValues16
open R0P PV_RunJoin_OutputModel16 PV_RunJoin_FixtureRecords
attribute [local irreducible] poseidonPermutation
'''
for label,a,pk,v,salt in [('recipient',30,300,600,400),('transfer_change',33,500,400,600),('withdrawal_change',36,700,750,800)]:
 s+=f'''def {label}_chunk2 : Fin 8 → Scalar := fun i =>
  if i.val = 0 then {v} else if i.val = 1 then 77 else (digest {salt}) ⟨i.val-2,by omega⟩
def {label}_chunk3 : Fin 8 → Scalar := fun i =>
  if h : i.val < 2 then (digest {salt}) ⟨i.val+6,by omega⟩ else 0

theorem {label}_init : absorb (spongeInit (0x41530003 : Scalar) 18) (digest {pk}) = s_{a}_0 := by
  funext i; fin_cases i <;> rfl

theorem {label}_absorb2 : absorb s_{a}_23 {label}_chunk2 = s_{a+1}_0 := by
  funext i; fin_cases i <;> rfl

theorem {label}_absorb3 : absorb s_{a+1}_23 {label}_chunk3 = s_{a+2}_0 := by
  funext i; fin_cases i <;> rfl

theorem {label} : noteCommitment (digest {pk}) ({v} : Scalar) 77 (digest {salt}) = digestOf s_{a+2}_23 := by
  change digestOf (spongeStep (spongeStep (spongeStep (spongeInit 0x41530003 18)
    (digest {pk})) {label}_chunk2) {label}_chunk3) = _
  unfold spongeStep
  rw [{label}_init,permutation_{a},{label}_absorb2,permutation_{a+1},{label}_absorb3,permutation_{a+2}]
#print axioms {label}_init
#print axioms {label}_absorb2
#print axioms {label}_absorb3
#print axioms {label}
'''
s+='end R1Z.PV_RunJoin_OutputValues16\n';n='PV_RunJoin_OutputValues16.lean'
if '--check' in sys.argv:assert (L/n).read_text()==s
else:(L/n).write_text(s)
print('output values generation/check passed')
