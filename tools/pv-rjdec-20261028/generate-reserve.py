"""Reify the reached wrapper call with the typed byte-array operation."""
from pathlib import Path
import re
root=Path('docs/research/v8-r0-zk-20261009/lean/R1Z')
s=(root/'PV_W_R_ReserveBuild.lean').read_text()
s=s.replace('namespace R1Z.PV_W_R_ReserveBuild','namespace R1Z.PV_RJDec_ReserveBuild').replace('end R1Z.PV_W_R_ReserveBuild','end R1Z.PV_RJDec_ReserveBuild')
s='import R1Z.PV_RJDec_ZeroizingSelected\n'+s
start=s.index('              let _ ← invoke "zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize"')
end=s.index('              pure (core.result.Result.Ok',start)
s=s[:start]+'              let _ ← perform (.zeroArray 32#usize self.field_mask_entropy)\n'+s[end:]
a=s.index('theorem erase_program');b=s.index('\n#print axioms',a)
t=s[a:b]
t=re.sub(r'\bops\b','(PV_RJDec_ZeroizingSelected.selected ops)',t)
t=t.replace('(ops : ExternalFuns)','(ops : ExternalFuns)') # binder repaired below
t=t.replace('((PV_RJDec_ZeroizingSelected.selected ops) : ExternalFuns)','(ops : ExternalFuns)')
t=t.replace('exact erase_invoke (PV_RJDec_ZeroizingSelected.selected ops) _ _','first\n'+ ' '*6+'| exact erase_invoke (PV_RJDec_ZeroizingSelected.selected ops) _ _\n'+' '*6+'| (rw [erase_perform]; rfl)')
# Keep tactic alternatives at their original indentation.
lines=t.splitlines();out=[]
for line in lines:
 if '| exact erase_invoke' in line or '| (rw [erase_perform]' in line:
  indent=len(out[-1])-len(out[-1].lstrip()) if out[-1].strip()=='first' else len(out[-2])-len(out[-2].lstrip())
  line=' '*(indent+2)+line.lstrip()
 out.append(line)
s=s[:a]+'\n'.join(out)+s[b:]
(root/'PV_RJDec_ReserveBuild.lean').write_text(s)
