"""Propagate the typed reached call through the two existing caller bodies."""
from pathlib import Path
import re
root=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
for name,child in [('MaskedWithAttempt','ReserveBuild'),('Entry','MaskedWithAttempt')]:
 s=(root/('PV_W_R_'+name+'.lean')).read_text();s='import R1Z.PV_RJDec_'+child+'\n'+s
 s=s.replace('namespace R1Z.PV_W_R_'+name,'namespace R1Z.PV_RJDec_'+name).replace('end R1Z.PV_W_R_'+name,'end R1Z.PV_RJDec_'+name)
 s=s.replace('PV_W_R_'+child+'.program','PV_RJDec_'+child+'.program').replace('PV_W_R_'+child+'.erase_program','PV_RJDec_'+child+'.erase_program')
 a=s.index('theorem erase_program');b=s.index('\n#print axioms',a);t=re.sub(r'\bops\b','(PV_RJDec_ZeroizingSelected.selected ops)',s[a:b]);t=t.replace('((PV_RJDec_ZeroizingSelected.selected ops) : ExternalFuns)','(ops : ExternalFuns)');s=s[:a]+t+s[b:]
 (root/('PV_RJDec_'+name+'.lean')).write_text(s)
