#!/usr/bin/env python3
"""Require a deletion-only endpoint diff; retain every undischarged join."""
import pathlib,difflib,hashlib,json
H=pathlib.Path(__file__).resolve().parent;L=H.parent/'lean/R1Z'
def statement(file,name):
 s=(L/file).read_text();s=s[s.index('theorem '+name+'\n'):];return s[:s.index(' := by')]
a=statement('PrivacyR1FinalReleaseSource4.lean','privacy_R1_release_source4')
b=statement('PrivacyR1FinalReleaseSource5.lean','privacy_R1_release_source5')
n=b.replace('theorem privacy_R1_release_source5\n','theorem privacy_R1_release_source4\n',1)
assert a==n,'Undischarged source join or conclusion changed'
d=dict(before_module='R1Z.PrivacyR1FinalReleaseSource4',after_module='R1Z.PrivacyR1FinalReleaseSource5',before_sha256=hashlib.sha256(a.encode()).hexdigest(),after_sha256=hashlib.sha256(b.encode()).hexdigest(),signature_diff_excluding_name=list(difflib.unified_diff(a.splitlines(),n.splitlines())),deleted_premises=[],added_premises=[],deletion_only=True,strictly_weaker=False,conclusion_and_all_binders_identical=True)
(H/'builder-cont10-signature-audit.json').write_text(json.dumps(d,indent=2)+'\n')
p=H/'BUILDER-CONT10-20261021.md';s=p.read_text();marker='\n## Verbatim endpoint signature audit\n';s=s.split(marker)[0]
s+=marker+'''
No complete runtime or execution join was discharged. The binder/conclusion
diff is empty, excluding the theorem name: deletion-only with zero deletions,
not a strict weakening. No new or stronger premise is introduced. The error,
freshness term and strict <2^-100 conclusion are byte-identical.

Before, verbatim:

```lean
'''+a+'\n```\n\nAfter, verbatim:\n\n```lean\n'+b+'\n```\n';p.write_text(s)
print('All binders and complete conclusion identical; no strengthening or claimed deletion')
