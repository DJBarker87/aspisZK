#!/usr/bin/env python3
"""Compare V2 and V3 headline statements, normalizing final-colon placement."""
from pathlib import Path
import re, difflib, json, hashlib
HERE=Path(__file__).resolve().parent
P=HERE.parent.parent
old=(P/'lean/R1FinalSoundnessHeadlineV2.lean').read_text()
new=(P/'lean/R1FinalSoundnessHeadlineV3.lean').read_text()
def statement(s):
    s='theorem final_soundness'+s.split('theorem final_soundness',1)[1].split(' := by',1)[0]
    s=re.sub(r'/\-[\s\S]*?\-/', '', s)
    # A deleted final binder moves the signature's colon: normalize this syntax.
    s=s.replace('Q + 1161) :','Q + 1161)\n    :')
    return '\n'.join(x.rstrip() for x in s.splitlines() if x.strip())+'\n'
before=statement(old); after=statement(new)
removed='''    (h_M10_log_length : BoundaryEvidence s → ∀ H,
      (eval H (recorded D d P)).2.2 = true →
        (eval H (recorded D d P)).1.length ≤ Q + 1161)
'''
assert before.count(removed)==1
assert before.replace(removed,'')==after
assert 'open R1FinalSoundnessHeadlineV2' in new
assert 'structure Boundary' not in new
for name,value in [('v2-before.lean.txt',before),('v3-after.lean.txt',after)]: (HERE/name).write_text(value)
diff=''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='v2',tofile='v3'))
assert not any(s.startswith('+') and not s.startswith('+++') for s in diff.splitlines())
(HERE/'signature-deletion-only.diff').write_text(diff)
result={'status':'pass','deleted_premises':['h_M10_log_length'],'replacement_premises':[], 'all_other_binders_and_conclusion':'identical', 'boundary_types':'same V2 declarations, imported and opened; no new inventory', 'normalization':'comments and blank lines removed; final signature colon placed on its own line in both statements', 'source_sha256':hashlib.sha256(new.encode()).hexdigest()}
(HERE/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
