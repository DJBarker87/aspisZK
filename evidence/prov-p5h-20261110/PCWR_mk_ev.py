import re
D='PCWR_E001_emitted/raw/PCWR_ev/'
def strip(t):
    out=[]
    for l in t.split('\n'):
        if l.startswith('import ') or l.startswith('set_option maxHeartbeats') or l.startswith('set_option maxRecDepth'): continue
        out.append(l)
    return '\n'.join(out)
H='''-- PCWR_ item 3 probe: does the frozen-crate emission of compact::expand_values (PCWR_E001, original Aeneas, ON, 4bb3b3f) elaborate against the L187 closure library?
-- The Types, the External templates (axioms) and Funs are concatenated verbatim (imports and raised heartbeat headers dropped). No statement is proved here.
import Aeneas
'''
t=H+strip(open(D+'TypesExternal_Template.lean').read())+'\n'+strip(open(D+'Types.lean').read())+'\n'+strip(open(D+'FunsExternal_Template.lean').read())+'\n'+strip(open(D+'Funs.lean').read())
open('PRVEq_S1ValuesOwnedModelV1_p1.lean','w').write(t)
