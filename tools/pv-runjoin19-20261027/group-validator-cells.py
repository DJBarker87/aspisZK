from pathlib import Path
import re,sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
for start in range(1,81,3):
 imports=[];bodies=[]
 for j in range(start,min(start+3,81)):
  s=(R/f'evidence/pv-runjoin19-20261027/cell-drafts/PV_RunJoin_ValidatorCell{j:02}19.lean.txt').read_text();imports+=re.findall(r'^import .*',s,re.M);bodies.append(s[s.index('set_option'):])
 s='\n'.join(dict.fromkeys(imports))+'\n'+'\n'.join(bodies);p=L/f'PV_RunJoin_ValidatorGroup{start:02}19.lean'
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
print('27 three-cell bounded groups (last two cells); first cell compiled separately')
