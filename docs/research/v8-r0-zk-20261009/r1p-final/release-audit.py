#!/usr/bin/env python3
"""Exact signature comparison of the D94/D96 reductions and composed endpoint."""
import hashlib, json, pathlib, re
HERE=pathlib.Path(__file__).resolve().parent
LEAN=HERE.parent/'lean/R1Z'
def statement(file, name):
    s=(LEAN/file).read_text(); start=s.index('theorem '+name+'\n')
    return s[start:s.index(' := by',start)]
def norm(s):
    return re.sub(r'\s+', ' ', s.replace('(h).','h.')).strip()
def binders(s):
    s=s[s.index('\n')+1:]; result=[]; i=0
    while i<len(s):
        if s[i]==':': break
        if s[i] not in '([': i+=1; continue
        start=i; stack=[s[i]]; i+=1
        while stack:
            ch=s[i]
            if ch in '([{': stack.append(ch)
            elif ch in ')]}':
                assert {'(':')','[':']','{':'}'}[stack.pop()]==ch
            i+=1
        b=s[start:i]; name=b[1:].split(':')[0].strip()
        result.append((name,norm(b)))
    return dict(result)
d94=statement('PrivacyR1FinalProtocolHistoryReal.lean','privacy_R1_protocol_history_real')
d96=statement('PrivacyR1FinalProtocolBuilder.lean','privacy_R1_protocol_builder')
release=statement('PrivacyR1FinalRelease.lean','privacy_R1_release')
a,b,c=map(binders,(d94,d96,release))
removed=['hpub','builder_refinement_D46_D51']
assert set(a)-set(c)==set(removed)
assert set(c)-set(a)==set()
assert all(c[k]==a[k] for k in c)
changed=[k for k in c if c[k]!=b[k]]
assert changed==['R_wire_builder_checker_D75_retry','G_sim_R_wire']
assert norm(d94[d94.index(' :\n    ZK_FSS'):])==norm(release[release.index(' :\n    ZK_FSS'):])
assert 'BuilderProtocolInstance.builder_sound B x' in (LEAN/'PrivacyR1FinalRelease.lean').read_text()
rec=dict(d94_removed=removed,d94_retained_identical=list(c),d94_conclusion_identical=True,
         d96_retained_identical=[k for k in c if k not in changed],d96_execution_replacements=changed,
         specialization='h := BuilderSource.prover (K := WideExact); public width := pubBytes.length',
         source_identification_claim=False,
         files={f:hashlib.sha256((LEAN/f).read_bytes()).hexdigest() for f in ['PrivacyR1FinalProtocolHistoryReal.lean','PrivacyR1FinalProtocolBuilder.lean','PrivacyR1FinalRelease.lean']})
(HERE/'release-signature-audit.json').write_text(json.dumps(rec,indent=2)+'\n')
print('PASS: D94 exact deletions and unchanged conclusion; D96 all common binders identical except the two D94 execution joins')
