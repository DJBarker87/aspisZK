from pathlib import Path
import re,json
R=Path(__file__).resolve().parents[2];L=R/'lean'
mapping={'SAF_C_SAP_LiteralFull':'P2P_LiteralFull','SAF_C_SAP_LiteralTop':'P2P_LiteralTop'}
chain=[('SAF_C_Rc3_Result','R3Result'),('SAF_C_Rc3_Top','R3Top'),('SAF_C_SAF_Result','SafResult'),('SAF_C_SAF_Top','SafTop'),('SAF_C_SAF_FinalResult','FinalResult'),('SAF_C_SAF_FinalTop','FinalTop'),('SAF_Deployed','Deployed'),('Rc5_Result','R5Result'),('Rc5_Close','R5Close'),('Rc6_Result','R6Result')]
for old,label in chain:
 new='P2P_'+label;s=(L/(old+'.lean')).read_text();preds={k:v for k,v in mapping.items() if k+'.' in s}
 s='import P2P_Origin\n'+''.join('import '+v+'\n' for v in preds.values())+s
 s=s.replace('AspisR1.'+old,'AspisR1.'+new)
 for k,v in preds.items():s=s.replace(k+'.',v+'.')
 if '∃ tx2 : Cons_Native.Witness,' in s:
  d='(sdkOps (Tx2I_Install.install adapterOps (Op5T_Concrete.stage (Tx2N_Execution.control (AuS1_Install.base stageBase) reserved queryOps geoOps)) finishOps) (Uni_Install.current ops reserved queryOps geoOps) (F3M_CircleSource.install B) (NP6_StdModel.calls reservation))'
  s=s.replace('    ∃ tx2 : Cons_Native.Witness,','    ∃ tx2 : Cons_Native.Witness,\n      P2P_Origin.Fact '+d+' program (e2.second secondSizes) data2 slot s ∧')
 s=re.sub(r'(⟨f,\s*s,\s*outer,\s*pre,\s*middle,\s*fs,\s*ss,\s*run,\s*tx2,)',r'\1origin,',s)
 s=re.sub(r'^#print (?!axioms).*\n','',s,flags=re.M)
 (L/(new+'.lean')).write_text(s);mapping[old]=new
# Extract the new checked source conjuncts with the existing tactic pattern.
s=(L/'Rc5_Extract.lean').read_text().replace('rc5_extract_saf_source','p2p_extract_source')
for k,v in mapping.items():s=s.replace(k,v)
s='import P2P_Deployed\n'+s
(L/'P2P_Extract.lean').write_text(s)
s=(L/'Rc5_Source.lean').read_text().replace('AspisR1.Rc5_Source','AspisR1.P2P_Source').replace('rc5_extract_saf_source','p2p_extract_source').replace('SAF_C_SAF_FinalResult.','P2P_FinalResult.')
s='import P2P_Extract\nimport P2P_FinalResult\n'+s
(L/'P2P_Source.lean').write_text(s)
mapping['Rc5_Source']='P2P_Source'
for old,label in [('Rc5_Top','R5Top'),('Rc6_Top','R6Top')]:
 new='P2P_'+label;s=(L/(old+'.lean')).read_text();preds={k:v for k,v in mapping.items() if k+'.' in s}
 s=''.join('import '+v+'\n' for v in preds.values())+s
 s=s.replace('AspisR1.'+old,'AspisR1.'+new)
 for k,v in preds.items():s=s.replace(k+'.',v+'.')
 (L/(new+'.lean')).write_text(s);mapping[old]=new
(R/'evidence/p2prime-20261026/P2P_root_mapping.json').write_text(json.dumps(mapping,indent=2)+'\n')
