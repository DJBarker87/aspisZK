from pathlib import Path
import re,json
R=Path(__file__).resolve().parents[2];L=R/'lean'
mapping=json.loads((R/'evidence/p2prime-20261026/P2P_provenance_mapping.json').read_text())
pairs=[('ResultSelected','SAF_C_SAP_ResultSelected'),('PairSelected','SAF_C_SAP_PairSelected'),('ActualResult','SAF_C_SAP_ActualResult'),('ActualPair','SAF_C_SAP_ActualPair'),('ClosedResult','SAF_C_SAP_ClosedResult'),('ClosedPair','SAF_C_SAP_ClosedPair'),('DirectResult','SAF_C_SAP_DirectResult'),('DirectPair','SAF_C_SAP_DirectPair'),('LiteralResult','SAF_C_SAP_LiteralResult'),('LiteralPair','SAF_C_SAP_LiteralPair'),('LiteralFull','SAF_C_SAP_LiteralFull'),('LiteralTop','SAF_C_SAP_LiteralTop')]
for label,old in pairs:
 new='P2P_'+label;s=(L/(old+'.lean')).read_text()
 s='import P2P_Origin\n'+''.join('import '+v+'\n' for k,v in mapping.items() if k+'.' in s)+s
 s=s.replace('AspisR1.'+old,'AspisR1.'+new)
 for k,v in mapping.items():s=s.replace(k+'.',v+'.')
 # The full result changes separately at its named existential.
 if label.endswith('Result') or label in ['ResultSelected','LiteralFull']:
  B='B' if label=='ResultSelected' else '(F3M_CircleSource.install B)'
  d=f'(sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) {B} claimsStd)'
  s=s.replace('    ∃ tx2 : Cons_Native.Witness,','    ∃ tx2 : Cons_Native.Witness,\n      P2P_Origin.Fact '+d+' program (e2.second secondSizes) data2 slot s ∧')
 else:
  s=re.sub(r'(⟨f,\s*s,\s*outer,\s*pre,\s*middle,\s*fs,\s*ss,\s*run,\s*tx2(?:run)?,)',r'\1origin,',s)
  if label=='PairSelected':
   s=s.replace('fs,ss,cuts,selected','fs,ss,cuts,origin,selected')
  # The LiteralTop result type is transformed through LiteralFull.
 s=re.sub(r'^#print (?!axioms).*\n','',s,flags=re.M)
 (L/(new+'.lean')).write_text(s);mapping[old]=new
(R/'evidence/p2prime-20261026/P2P_late_mapping.json').write_text(json.dumps(mapping,indent=2)+'\n')
