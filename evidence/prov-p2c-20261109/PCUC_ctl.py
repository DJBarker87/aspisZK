#!/usr/bin/env python3
"""PCUC_ctl.py: self-copy control (PCO_HANDOFF section 4). The gate candidate text, namespace renamed, is the 'fresh emission'; require 100% rfl vs the compiled gate."""
import re,subprocess,sys,json
from pathlib import Path
sys.dont_write_bytecode=True
import PCUC_gen_equalities as G
specs=[('AspisR1TerminalDecoder.Funs','AspisR1TerminalDecoder_Funs','inputs/gate_AspisR1TerminalDecoder_Funs.lean','inputs/gatetypes_AspisR1TerminalDecoder_Funs.lean'),
       ('NFY_Part043','NFY_Part043','inputs/gate_NFY_Part043.lean','inputs/gatetypes_NFY_Part043.lean'),
       ('Port23PUSH_Source','Port23PUSH_Source','inputs/gate_Port23PUSH_Source.lean','inputs/gate_Port23PUSH_Source.lean')]
for m,safe,gp,gtp in specs:
    t=Path(gp).read_text();ns=G.header_info(t)['namespaces'][0];new='CTL'+ns
    t2=re.sub(r'(?m)^namespace '+re.escape(ns)+r'\s*$','namespace '+new,t);t2=re.sub(r'(?m)^end '+re.escape(ns)+r'\s*$','end '+new,t2)
    d=Path('ctl/fresh_'+safe);d.mkdir(parents=True,exist_ok=True);(d/'Funs.lean').write_text(t2);(d/'Types.lean').write_text(t2)
    lab=safe+'_CTL'
    c=['python3','-B','PCUC_gen_equalities.py','--partition','PCUC_PARTITION.json','--module',m,'--tag','_CTL','--fresh-dir',str(d),'--fresh-ns',new,'--gate-source',gp,'--gate-types-source',gtp,
       '--out',f'PRVEq_{lab}.lean','--report',f'gen/PRVEq_{lab}.report1.json','--state-out',f'gen/PRVEq_{lab}.state1.json']
    p=subprocess.run(c,capture_output=True,text=True);print(lab,p.returncode,p.stderr.strip()[-300:])
