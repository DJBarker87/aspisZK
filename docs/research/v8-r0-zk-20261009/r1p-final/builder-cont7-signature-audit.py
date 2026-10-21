#!/usr/bin/env python3
"""Check the exact endpoint statement, preserving the complete source joins."""
import difflib, hashlib, json, pathlib
HERE = pathlib.Path(__file__).resolve().parent
LEAN = HERE.parent/'lean/R1Z'
a = (LEAN/'PrivacyR1FinalReleaseSource.lean').read_text()
b = (LEAN/'PrivacyR1FinalReleaseSource2.lean').read_text()
def statement(s, name):
    s=s[s.index('theorem '+name+'\n'):]
    return s[:s.index(' := by')]
a=statement(a,'privacy_R1_release_source')
b=statement(b,'privacy_R1_release_source2')
normalized=b.replace('theorem privacy_R1_release_source2\n','theorem privacy_R1_release_source\n',1)
assert normalized == a, 'a premise or conclusion changed without a discharge certificate'
rec=dict(before_module='R1Z.PrivacyR1FinalReleaseSource',after_module='R1Z.PrivacyR1FinalReleaseSource2',
    before_sha256=hashlib.sha256(a.encode()).hexdigest(),after_sha256=hashlib.sha256(b.encode()).hexdigest(),
    signature_diff_excluding_name=list(difflib.unified_diff(a.splitlines(),normalized.splitlines())),
    deleted_premises=[],added_premises=[],deletion_only=True,strictly_weaker=False,
    conclusion_and_all_binders_identical=True)
(HERE/'builder-cont7-signature-audit.json').write_text(json.dumps(rec,indent=2)+'\n')
p=HERE/'BUILDER-CONT7-20261021.md';s=p.read_text();marker='\n## Verbatim endpoint signature audit\n'
if marker in s:s=s[:s.index(marker)]
s+=marker+'''
No source premise is discharged by the partial component theorem. Thus the
binder/conclusion diff, excluding the theorem name, is empty: deletion-only
with zero deletions, **not** a strict weakening. Both runtime and execution
joins remain. The new endpoint preserves the inherited freshness error and
strict <2^-100 conclusion. No stronger premise replaces an inherited one.
The audit script asserts complete binder and conclusion identity.

Before, verbatim:

```lean
'''+a+'\n```\n\nAfter, verbatim:\n\n```lean\n'+b+'\n```\n'
p.write_text(s)
print(json.dumps(rec,indent=2))
