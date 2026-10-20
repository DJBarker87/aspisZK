#!/usr/bin/env python3
import difflib,hashlib,json
from pathlib import Path
E=Path(__file__).resolve().parent.parent
R=Path('docs/research/v8-r0-zk-20261009')
def signature(name,file):
 s=(R/'lean/R1Z'/file).read_text();a=s.index('theorem '+name+'\n');b=s.index(' := by',a)
 return s[a:b]
a=signature('privacy_R1_protocol_history_real','PrivacyR1FinalProtocolHistoryReal.lean')
b=signature('privacy_R1_protocol_quotient','PrivacyR1FinalProtocolQuotient.lean')
pr='((prover base ((base.pubBytes x).length) h B outputs x seed).toProver)'
normalized=b.replace('privacy_R1_protocol_quotient','privacy_R1_protocol_history_real').replace('R_commit_quotient_fibres','R_commit_equal_fibres').replace('∀ τ : SourceTape K F','∀ τ : Tape K F').replace('quotientDecode (fun e => '+pr+'.tapeOf e.1 e.2) e',pr+'.tapeOf e.1 e.2')
assert normalized==a
key=' :\n    ZK_FSS'
assert a[a.index(key):]==b[b.index(key):]
for name,text in [('signature-before.txt',a),('signature-after.txt',b)]: (E/name).write_text(text+'\n')
diff=''.join(difflib.unified_diff(a.splitlines(True),b.splitlines(True),fromfile='PrivacyR1FinalProtocolHistoryReal',tofile='PrivacyR1FinalProtocolQuotient'))
(E/'signature.diff').write_text(diff)
(E/'signature-check.json').write_text(json.dumps(dict(conclusion_byte_identical=True,all_other_binders_byte_identical=True,
 old_signature_sha256=hashlib.sha256(a.encode()).hexdigest(),new_signature_sha256=hashlib.sha256(b.encode()).hexdigest(),
 only_changes=['theorem name','R_commit_equal_fibres renamed R_commit_quotient_fibres','Tape replaced with SourceTape in fibre quantifier','decoder composed with Option.map project']),indent=2)+'\n')
print(diff)
