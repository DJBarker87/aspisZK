#!/bin/bash
# PCWL: AdapterRwModel require_zero (frozen slice loop, PCWL_E001 fresh text) = gate require_zero (index loop); extensional equality for all inputs.
cd "$(dirname "$0")"
python3 -B - <<'P'
import re
F=open('PCWL_E001_emitted/raw/PCWL_ar/Funs.lean').read()
blocks=re.split(r'\n(?=/--)',F)
def get(name):
    for b in blocks:
        if re.search(r'\ndef '+re.escape(name)+r'(?![\w.])',b): return re.sub(r'\nend PCWL_ar\s*$','',b.strip('\n'))
    raise SystemExit('missing '+name)
fb=get('r1_pool_adapter.owned.require_zero_loop.body');fl=get('r1_pool_adapter.owned.require_zero_loop')
fz=get('r1_pool_adapter.owned.require_zero')
H=open('PCWL_rz_head.lean').read();T=open('PCWL_rz_tail.lean').read()
open('PRVEq_AdapterRwModel_w7.lean','w').write(H+fb+'\n\n'+fl+'\n\n'+fz+'\n'+T)
P
