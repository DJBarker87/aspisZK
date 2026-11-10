#!/usr/bin/env python3
"""PCWN: composite fresh Types input for Stage2ContinuationTypes: PCVX_E012 (frozen 4bb3b3f cost-probe emission, namespace PCVX_tx2s; WideExact external there)
plus the WideExact structure copied verbatim from PCVJ_E002 (frozen 4bb3b3f aspis-core emission, namespace PCVJ_top), inserted after QM31."""
import re
a=open('inputs/E012_s2/Types.lean').read();b=open('inputs/PCVJ_top/Types.lean').read()
m=re.search(r'/-- \[aspis_core::field::wide_exact::WideExact\].*?c1 : aspis_core\.field\.QM31\n',b,re.S);assert m
blk=m.group(0)
i=a.index('/-- [aspis_core::circle::SecureCirclePoint]')
open('inputs/E012_s2/Types_composite.lean','w').write(a[:i]+blk+'\n'+a[i:])
