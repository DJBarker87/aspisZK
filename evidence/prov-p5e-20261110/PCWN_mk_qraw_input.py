#!/usr/bin/env python3
"""PCWN: derive the QRaw fresh Types input from the frozen E015 Types text (PCQK_E015, namespace PCQK_cp) by a recorded name substitution:
fast_pairing.canonical.Q -> canonical.Q ; fast_pairing.canonical.Q.raw.closure -> canonical.Q.raw.closure_2 (the gate closure_2 is the u64->u64 callback, PCVZ closure_call).
Only those two declarations are kept. Writes inputs/E015_qraw/Types.lean."""
import re,os
s=open('inputs/E015_cp/Types.lean').read()
head=s[:s.index('namespace PCQK_cp')]
def decl(name):
    m=re.search(r'(?s)(/-- \['+re.escape('aspis_r1_cost_probe::'+name)+r'\].*?\n)(?=\n/--|\nend PCQK_cp)',s); return None
blocks=re.split(r'\n\n(?=/-- \[)',s)
keep=[b for b in blocks if re.search(r'def fast_pairing\.canonical\.Q( |\n)',b) or re.search(r'def fast_pairing\.canonical\.Q\.raw\.closure( |\n)',b)]
assert len(keep)==2,len(keep)
out=[]
for b in keep:
    b=b.replace('fast_pairing.canonical.Q.raw.closure','canonical.Q.raw.closure_2').replace('def fast_pairing.canonical.Q ','def canonical.Q ')
    out.append(b.strip('\n'))
os.makedirs('inputs/E015_qraw',exist_ok=True)
open('inputs/E015_qraw/Types.lean','w').write(head+'namespace PCQK_cp\n\n'+'\n\n'.join(out)+'\n\nend PCQK_cp\n')
