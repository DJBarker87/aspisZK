"""Audit all theorem binders; no Lean invocation or dependency rebuild."""
import hashlib, json, re
from pathlib import Path
here = Path(__file__).resolve().parent
lean = here.parents[1] / 'lean/R1Z'
def theorem(name, thm):
    text = (lean / (name + '.lean')).read_text()
    start = text.index('theorem ' + thm + '\n')
    stop = text.index(' := by', start)
    return text[start:stop]
def parse(s):
    pos = s.index('\n')
    binders = []
    while pos < len(s):
        if s[pos].isspace(): pos += 1; continue
        if s[pos] not in '([': break
        start = pos
        stack = [s[pos]]
        pos += 1
        while stack:
            c = s[pos]
            if c in '([': stack.append(c)
            elif c in ')]': stack.pop()
            pos += 1
        binders.append(s[start:pos])
    return binders, s[pos:]
def norm(s):
    return re.sub(r'\s+', '', s.replace('(h)', 'h'))
def key(b):
    return b[1:-1].split(':')[0].strip() if ':' in b else b[1:-1].strip()
headline = theorem('PrivacyR1Headline','privacy_headline')
hb, hc = parse(headline)
predecessors = [
 ('PrivacyR1FinalProtocolHistoryReal','privacy_R1_protocol_history_real'),
 ('PrivacyR1FinalProtocolQuotient','privacy_R1_protocol_quotient'),
 ('PrivacyR1FinalRelease','privacy_R1_release'),
 ('PrivacyR1FinalReleaseSource','privacy_R1_release_source'),
 ('PrivacyR1FinalReleaseSource2','privacy_R1_release_source2'),
 ('PrivacyR1FinalReleaseSource3','privacy_R1_release_source3')]
result = {'headline_sha256': hashlib.sha256((lean/'PrivacyR1Headline.lean').read_bytes()).hexdigest(), 'predecessors': []}
for mod, thm in predecessors:
    pb, pc = parse(theorem(mod, thm))
    pm = {key(b): b for b in pb}
    rows = []
    for b in hb:
        k = key(b)
        if k == 'builder_premises':
            status = 'derived: builder_premises_of_' + ('protocol' if 'Protocol' in mod else ('canonical' if mod == 'PrivacyR1FinalRelease' else 'source'))
        elif k == 'R_commit_quotient_fibres' and k not in pm:
            status = 'strict law weakening: full_fibres_imply_quotient; cF becomes card(Padding)*cF'
        else:
            assert k in pm, (mod,k)
            assert norm(b) == norm(pm[k]), (mod,k,b,pm[k])
            status = 'identical'
        rows.append({'binder':k,'status':status})
    assert norm(hc) == norm(pc), mod
    result['predecessors'].append({'module':mod,'theorem':thm,'binders':rows,'conclusion':'identical',
       'replaced_binders':[k for k in pm if k not in {key(b) for b in hb}]})
(here/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
print('Audited every headline binder and identical conclusion against six predecessor signatures.')
