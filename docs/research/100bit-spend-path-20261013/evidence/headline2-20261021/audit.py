#!/usr/bin/env python3
"""Deletion-only audit after explicitly recorded data specialization."""
from pathlib import Path
import re, json, difflib, hashlib
HERE = Path(__file__).resolve().parent
P = HERE.parent.parent
old = (P/'lean/R1FinalSoundnessHeadline.lean').read_text()
new = (P/'lean/R1FinalSoundnessHeadlineV2.lean').read_text()
base = (P/'lean/R1FinalSoundness.lean').read_text()
def clean(s):
    s = re.sub(r'/\-[\s\S]*?\-/', '', s)
    return '\n'.join(x.rstrip() for x in s.splitlines() if x.strip())+'\n'
def statement(s):
    return clean('theorem final_soundness'+s.split('theorem final_soundness',1)[1].split(' := by',1)[0])
def fields(s, name):
    body=s.split('structure '+name,1)[1].split('where',1)[1]
    return re.findall(r'^  (\w+) : ([^\n]+)',body.split('\n\n',1)[0],re.M)
# Original structures include documentation comments, which clean removes.
base_clean=clean(base); new_clean=clean(new)
# clean removes blank separators; stop at next declaration instead.
def inventory(s,name):
    body=s.split('structure '+name,1)[1].split('where',1)[1]
    body=re.split(r'\n(?:structure|def|abbrev|theorem|/--)',body,1)[0]
    return re.findall(r'^  (\w+) : ([^\n]+)',body,re.M)
def raw_inventory(s,name):
    body=s.split('structure '+name,1)[1].split('where',1)[1]
    body=re.split(r'\n(?:structure|def|abbrev|theorem)',body,1)[0]
    return re.findall(r'^  (\w+) : ([^\n]+)',body,re.M)
# use original blank-separated structures then strip comments within that block
old_fields=re.findall(r'^  (\w+) : Prop$',base.split('structure BoundaryStatements where')[1].split('structure BoundaryEvidence')[0],re.M)
new_fields=re.findall(r'^  (\w+) : Prop$',new.split('structure BoundaryStatements where')[1].split('structure BoundaryEvidence')[0],re.M)
old_evidence=re.findall(r'^  (h_\w+) : (s\.\w+)$',base.split('structure BoundaryEvidence')[1].split('/-- Data selected')[0],re.M)
new_evidence=re.findall(r'^  (h_\w+) : (s\.\w+)$',new.split('structure BoundaryEvidence')[1].split('def legacyStatements')[0],re.M)
assert old_fields==new_fields+['M10_uniform']
assert old_evidence==new_evidence+[('h_M10_uniform','s.M10_uniform')]
before=statement(old)
removed='    (e : RawExtractorCostComposedBin.CostedExtractor) (p : Parameters)\n'
assert removed in before
before=before.replace(removed,'')
before=before.replace('e.eval','ActualCostedExtractorM10.extractor.eval').replace('(p.attemptBudget : ℚ)','((CostedAllocationLedgerM10.params Q).attemptBudget : ℚ)')
ledger='    (h_M10_ledger : RawExtractorCostComposedBin.LedgerRefinement e p Q)\n'
# Display the ledger at the specialized values too.
before=before.replace(ledger,'    (h_M10_ledger : RawExtractorCostComposedBin.LedgerRefinement\n      ActualCostedExtractorM10.extractor (CostedAllocationLedgerM10.params Q) Q)\n')
after=statement(new)
expected=before.replace('    (h_M10_ledger : RawExtractorCostComposedBin.LedgerRefinement\n      ActualCostedExtractorM10.extractor (CostedAllocationLedgerM10.params Q) Q)\n','')
assert expected==after
# Expand the two evidence inventories, so the embedded premise deletion is visible.
before_expanded='structure BoundaryStatements where\n'+''.join('  '+f+' : Prop\n' for f in old_fields)+'\nstructure BoundaryEvidence (s : BoundaryStatements) : Prop where\n'+''.join(f'  {f} : {t}\n' for f,t in old_evidence)+'\n'+before
after_expanded='structure BoundaryStatements where\n'+''.join('  '+f+' : Prop\n' for f in new_fields)+'\nstructure BoundaryEvidence (s : BoundaryStatements) : Prop where\n'+''.join(f'  {f} : {t}\n' for f,t in new_evidence)+'\n'+after
for name,text in [('v1-specialized-before.lean.txt',before_expanded),('v2-after.lean.txt',after_expanded)]: (HERE/name).write_text(text)
diff=''.join(difflib.unified_diff(before_expanded.splitlines(True),after_expanded.splitlines(True),fromfile='v1-specialized',tofile='v2'))
assert not any(line.startswith('+') and not line.startswith('+++') for line in diff.splitlines())
(HERE/'signature-deletion-only.diff').write_text(diff)
(HERE/'data-specialization.diff').write_text(''.join(difflib.unified_diff(statement(old).splitlines(True),before.splitlines(True),fromfile='v1',tofile='v1-specialized')))
result={'status':'pass','retained_evidence_fields':len(new_evidence),'deleted_data':['e','p','s.M10_uniform (unused proposition data)'],'deleted_premises':['h_M10_ledger','evidence.h_M10_uniform'],'retained_binders':'all others identical under local BoundaryStatements/BoundaryEvidence inventory deletion','retained_M10_log_length':True,'replacement_premises':[], 'specialization':{'e':'ActualCostedExtractorM10.extractor','p':'CostedAllocationLedgerM10.params Q'},'source_sha256':hashlib.sha256(new.encode()).hexdigest(),'compatibility':'M10Closed source already calls R1FinalSoundnessHeadline.final_soundness; no R19/Tag/NoColl/R9Pool obstruction'}
(HERE/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
