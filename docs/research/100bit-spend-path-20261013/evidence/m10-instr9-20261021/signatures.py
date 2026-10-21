#!/usr/bin/env python3
"""Pin the endpoint's declaration and deletion-only premise change."""
import difflib, hashlib, json, re
from pathlib import Path
HERE=Path(__file__).resolve().parent
PACKET=HERE.parent.parent
old=(PACKET/'lean/R1FinalSoundnessBinPerQueryM10.lean').read_text()
new=(PACKET/'lean/R1FinalSoundnessBinPerQueryM10Closed.lean').read_text()
def binders(s):
    a=s.index('theorem final_soundness')
    b=s.index(' :\n    (∀ H : Bytes',a)
    return s[a:b]
a,b=binders(old),binders(new)
removed='''    (heap : CostedAllocationLedgerM10.HeapMirror)
    /- Strict residual: cumulative allocation bit work on the same domain. -/
    (h_M10_allocation : CostedAllocationLedgerM10.AllocationBound heap Q)
'''
assert removed in a
assert a.replace(removed,'')==b
patch=''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True),
    fromfile='R1FinalSoundnessBinPerQueryM10.final_soundness premises',
    tofile='R1FinalSoundnessBinPerQueryM10Closed.final_soundness premises'))
assert not any(line.startswith('+') and not line.startswith('+++') for line in patch.splitlines())
(HERE/'premise-deletion.diff').write_text(patch+'\n')
(HERE/'before-signature.lean.txt').write_text(a+'\n')
(HERE/'after-signature.lean.txt').write_text(b+'\n')
data={
 'old_endpoint':'AspisR1.R1FinalSoundnessBinPerQueryM10.final_soundness',
 'new_endpoint':'AspisR1.R1FinalSoundnessBinPerQueryM10Closed.final_soundness',
 'binder_change':'deletion only',
 'removed_verbatim':['(heap : CostedAllocationLedgerM10.HeapMirror)',
   '(h_M10_allocation : CostedAllocationLedgerM10.AllocationBound heap Q)'],
 'new_implementation_premises':[],
 'unchanged_log_length_verbatim':'''(h_M10_log_length : BoundaryEvidence s → ∀ H,
      (eval H (recorded D d P)).2.2 = true →
        (eval H (recorded D d P)).1.length ≤ Q + 1161)''',
 'allocation_width':1024,
 'allocation_linear_constant':'1024*CostedAllocationLedgerM10.workConstant',
 'cost_polynomial':'CostedAllocationLedgerM10.costPolynomial',
 'direct_cost_polynomial':'4*CostedAllocationLedgerM10.scale^3*(Q+1162)^3',
 'degree_at_most':3,
 'old_endpoint_sha256':hashlib.sha256(old.encode()).hexdigest(),
 'new_endpoint_sha256':hashlib.sha256(new.encode()).hexdigest(),
 'model':'cumulative fixed-slot constructor tariff; task-specified fixed-width field operations',
 'accepted_run_scope':'accepted-flag RunView in the AllocationBound domain; no experiment-existence claim'}
(HERE/'requested-outcomes.json').write_text(json.dumps(data,indent=2)+'\n')
print('Deletion-only premise comparison passed')
