"""Generate a Formatter-carrier erasure adapter, not a native representation."""
from pathlib import Path
import re,sys
r=Path(__file__).resolve().parents[2];p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s='''import R1Z.PDict_FmtRetryComplete
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtCarrier
open Aeneas Aeneas.Std Result ProverRwFull
@[reducible] def eraseType (base : ExternalTypes) : ExternalTypes :=
  { base with op27 := Empty }
/-- All real operation fields are retained. The only removed carrier and callback
are Formatter/Debug, which the retry execution never invokes. This is an erased
interpreter for comparison, not an asserted native Formatter representation. -/
@[reducible] def eraseOps (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns (eraseType base) :=
  letI : ExternalTypes := eraseType base
  {
'''
for i in range(262):s+=('  op85 := fun _ impossible => nomatch impossible\n' if i==85 else f'  op{i} := @ExternalFuns.op{i} base ops\n')
s+='''}
theorem type27_erased (base : ExternalTypes) : (eraseType base).op27 = Empty := rfl
#print axioms type27_erased
end R1Z.PDict_FmtCarrier
'''
t=p/'PDict_FmtCarrierBase.lean'
if '--check' in sys.argv:assert t.read_text()==s
else:t.write_text(s)
