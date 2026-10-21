#!/usr/bin/env python3
"""Exact headline specialization, explicit narrowing, and deletion-only core."""
from pathlib import Path
import difflib, hashlib, json, re
H=Path(__file__).resolve().parent
P=H.parent.parent
before=(P/'lean/R1FinalSoundnessHeadline.lean').read_text()
after=(P/'lean/R1FinalSoundnessBinPerQueryM10.lean').read_text()
def statement(s):
    return s[s.index('theorem final_soundness'):s.index(' := by',s.index('theorem final_soundness'))]
def normalize(s):
    s=re.sub(r'/\-[\s\S]*?\-/','',s)
    return re.sub(r'\s+',' ',s).strip()
b=statement(before)
a=statement(after)
ledger='    (h_M10_ledger : RawExtractorCostComposedBin.LedgerRefinement e p Q)'
special=b.replace('    (e : RawExtractorCostComposedBin.CostedExtractor) (p : Parameters)',
    '    (heap : CostedAllocationLedgerM10.HeapMirror)')
special=special.replace('((e.eval ', '(((CostedAllocationLedgerM10.extractor heap).eval ')
special=special.replace('(e.eval run coins)', '((CostedAllocationLedgerM10.extractor heap).eval run coins)')
special=special.replace('(p.attemptBudget : ℚ)', '((CostedAllocationLedgerM10.params Q).attemptBudget : ℚ)')
newledger='    (h_M10_ledger : RawExtractorCostComposedBin.LedgerRefinement\n      (CostedAllocationLedgerM10.extractor heap) (CostedAllocationLedgerM10.params Q) Q)'
special=special.replace(ledger,newledger)
allocation='    (h_M10_allocation : CostedAllocationLedgerM10.AllocationBound heap Q)'
# After isolating the one residual component, deleting the total ledger binder
# is exact. The earlier introduction of allocation is separately visible.
core=special.replace(newledger, allocation+'\n'+newledger)
expected=core.replace(newledger+'\n','')
assert normalize(expected)==normalize(a), 'Unexpected signature difference'
for name,content in [('headline-before.lean.txt',b),('headline-specialized-before.lean.txt',special),
                     ('component-before-deletion.lean.txt',core),('m10-after.lean.txt',a)]:
    (H/name).write_text(content+'\n')
def diff(x,y,f,t): return ''.join(difflib.unified_diff(x.splitlines(True),y.splitlines(True),fromfile=f,tofile=t))
(H/'signature-deletion-only.diff').write_text(diff(core+'\n',expected+'\n','component-specialized-headline','m10'))
(H/'signature-specialization-and-narrowing.diff').write_text(diff(b+'\n',a+'\n','headline','m10'))
result={'status':'pass','base_headline_sha256':hashlib.sha256(before.encode()).hexdigest(),
 'endpoint_sha256':hashlib.sha256(after.encode()).hexdigest(),
 'unrelated_binders_and_conclusion_unchanged_after_extractor_specialization':True,
 'core_deletion_only':True,'headline_change':'specialize extractor/parameters and narrow ledger to one explicit allocation component',
 'unconditional_headline_deletion':False,'residual':'CostedAllocationLedgerM10.AllocationBound heap Q',
 'unchanged_experiment_premise':'h_M10_log_length'}
(H/'signature-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
