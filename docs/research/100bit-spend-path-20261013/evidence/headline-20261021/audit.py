#!/usr/bin/env python3
"""Reproducible signature audit; no Lean compilation or source mutation."""
from pathlib import Path
import difflib, hashlib, json, re
HERE = Path(__file__).resolve().parent
PACKET = HERE.parent.parent
L = PACKET / 'lean'
def statement(name):
    text = (L / (name + '.lean')).read_text()
    # Select the exact final_soundness declaration, not with_transport.
    start = text.index('theorem final_soundness\n')
    return text[start:text.index(' := by', start)]
def clean(s):
    s = re.sub(r'/\-[\s\S]*?\-/', '', s)
    return re.sub(r'\s+', ' ', s).strip()
def binders(s):
    s = clean(s).removeprefix('theorem final_soundness').strip()
    out = {}
    while s.startswith('('):
        depth = 0
        for i, c in enumerate(s):
            depth += (c == '(') - (c == ')')
            if depth == 0: break
        b = s[1:i]
        name, typ = b.split(' : ', 1)
        out[name] = typ
        s = s[i+1:].strip()
    assert s.startswith(':'), s
    return out, s
headline = statement('R1FinalSoundnessHeadline')
model = '(deployedFailureModel (tx1 D P tape) (poolTx2 D d P policy))'
def specialize(s):
    s = s.replace('(Q : Nat) (deployedFailure : ℚ)', '(Q : Nat) (tape : Tape) (policy : Policy)')
    s = s.replace('deployedFailure', model)
    return s
base = specialize(statement('R1FinalSoundnessBinPerQueryTag'))
old, result = binders(base)
new, newresult = binders(headline)
assert result == newresult
assert set(old) - set(new) == {'h_R9_transport'}
assert not set(new) - set(old)
assert all(old[k] == new[k] for k in new)
(HERE/'tag-specialized-before.lean.txt').write_text(base+'\n')
(HERE/'headline-after.lean.txt').write_text(headline+'\n')
(HERE/'signature-deletion-only.diff').write_text(''.join(difflib.unified_diff(base.splitlines(True), headline.splitlines(True), fromfile='Tag at constructed Pool instance', tofile='Headline')))
weakened = ['h_R16_instance','h_R13','h_R14_backend','h_R15_writer','h_R3_semantic']
nocoll = '¬ binaryCollision (Q + 1161) (eval H (recorded D d P)) → '
reports = []
for suffix in ['', 'Row31','R18','R19','RWire','NoColl','Tag','R9','R9Pool']:
    name = 'R1FinalSoundnessBinPerQuery'+suffix
    raw = statement(name)
    before = specialize(raw) if suffix not in ['R9','R9Pool'] else raw
    if suffix == 'R9':
        before = before.replace('(Q : Nat) (tx1 : Tx1) (poolTx2 : PoolTx2)', '(Q : Nat) (tape : Tape) (policy : Policy)')
        before = before.replace('deployedFailureModel tx1 poolTx2', 'deployedFailureModel (tx1 D P tape) (poolTx2 D d P policy)')
    b, conclusion = binders(before)
    assert conclusion == newresult, (name, conclusion, newresult)
    (HERE/(name+'-specialized.diff')).write_text(''.join(difflib.unified_diff(before.splitlines(True), headline.splitlines(True), fromfile=name+' specialized', tofile='Headline')))
    changes = {}
    for k,v in new.items():
        if k == 'h_Rwire_tag' and k not in b and 'h_Rwire' in b:
            continue
        assert k in b, (name,k)
        if b[k] == v: changes[k] = 'identical'
        elif k in weakened:
            assert v.replace(nocoll, '') == b[k], (name,k,b[k],v)
            changes[k] = 'weaker: NoCollPremiseWeakening.'+k+'_of_unconditional'
        elif k == 'h_Rwire_tag':
            assert 'RWireCompletion.InitialTag' in b[k]
            changes[k] = 'weaker: InitialTagDecision.checked_of_initialTag; checked_strictly_weaker'
        else: raise AssertionError((name,k,b[k],v))
    if 'h_Rwire' in b:
        changes['h_Rwire_tag'] = 'weaker: RWireCompletion.initialTag_of_completion then InitialTagDecision.checked_of_initialTag'
    allowed_deleted = {'h_R4_row31','h_R18','h_R19','h_Rwire','h_R9_transport'}
    assert set(b)-set(new) <= allowed_deleted, (name, set(b)-set(new))
    assert 'hN' not in b and 'hN' not in new
    reports.append({'module':name, 'source_sha256':hashlib.sha256((L/(name+'.lean')).read_bytes()).hexdigest(), 'premises':changes, 'deleted':sorted(set(b)-set(new))})
(HERE/'audit.json').write_text(json.dumps({'specialized_tag_deletion_only':True,'predecessors':reports},indent=2)+'\n')
print('Signature audit passed:',len(reports),'predecessors; specialized Tag differs only by deleting h_R9_transport')
