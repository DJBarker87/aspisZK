#!/usr/bin/env python3
"""PCWN: derive the Dot/EbyKDot fresh Types input from the frozen E015 Types text (PCQK_E015, namespace PCQK_cp) by the recorded prefix substitution
fast_pairing.canonical.{Q,Dot} -> canonical.{Q,Dot}, fast_pairing.EbyKDot -> EbyKDot. Only those three declarations are kept. Writes inputs/E015_dot/Types.lean."""
import re,os
s=open('inputs/E015_cp/Types.lean').read()
head=s[:s.index('namespace PCQK_cp')]
blocks=re.split(r'\n\n(?=/-- \[)',s)
pat=re.compile(r'(?:def|structure) fast_pairing\.(?:canonical\.Q|canonical\.Dot|EbyKDot)(?: |\n)')
keep=[b for b in blocks if pat.search(b)]
assert len(keep)==3,len(keep)
out=[b.strip('\n').replace('fast_pairing.EbyKDot','EbyKDot').replace('fast_pairing.canonical.','canonical.') for b in keep]
os.makedirs('inputs/E015_dot',exist_ok=True)
open('inputs/E015_dot/Types.lean','w').write(head+'namespace PCQK_cp\n\n'+'\n\n'.join(out)+'\n\nend PCQK_cp\n')
