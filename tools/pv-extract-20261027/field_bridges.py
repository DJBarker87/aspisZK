from pathlib import Path
import json,re
P=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');E=Path('evidence/pv-extract-20261027');rows=json.loads((E/'closed-split.json').read_text())['modules']; out=[];prev=None;lemmas=[]
for i,row in enumerate(rows[:-3]):
 full=row['declaration'];name=full.removeprefix('PV_Ext_IndexClosed.');tag=name.removeprefix('aspis_core.field.').replace('.','_');mod='PV_Ext_FieldBridge_'+tag
 imports='import '+row['module'].replace('/','.')+'\n'
 if prev:imports+='import R1Z.'+prev+'\n'
 old='R1Z.ProverRwP7CurrentFieldSource.'+name
 if tag=='M31_ZERO':rhs='(0#u32 : Aeneas.Std.U32)';proof='by rfl'
 elif tag=='CM31_ZERO':rhs='(⟨0#u32,0#u32⟩ : ProverRwFull.aspis_core.field.CM31)';proof='by rfl'
 elif tag=='CM31_from_m31':rhs='(fun x => Aeneas.Std.Result.ok (⟨x,0#u32⟩ : ProverRwFull.aspis_core.field.CM31))';proof='by\n  funext x\n  simp only [PV_Ext_IndexClosed.aspis_core.field.CM31.from_m31, PV_Ext_IndexClosed.aspis_core.field.M31.ZERO]'
 elif tag=='QM31_from_cm31':rhs='(fun x => Aeneas.Std.Result.ok (⟨x,⟨0#u32,0#u32⟩⟩ : ProverRwFull.aspis_core.field.QM31))';proof='by\n  funext x\n  simp only [PV_Ext_IndexClosed.aspis_core.field.QM31.from_cm31, PV_Ext_IndexClosed.aspis_core.field.CM31.ZERO]'
 else:
  rhs=old;proof='by rfl'
 ns='R1Z.PV_Ext_FieldBridge';s=imports+'open Aeneas Aeneas.Std Result\nnamespace '+ns+'\n/-- Exact complete-Result comparison of the freshly extracted candidate leaf\n    field dependency with the retained current source, on arbitrary raw limbs. -/\ntheorem '+tag+' : '+full+' = '+rhs+' := '+proof+'\n#print axioms '+tag+'\nend '+ns+'\n';(P/(mod+'.lean')).write_text(s);out.append(dict(module='R1Z/'+mod,theorem=ns+'.'+tag,source=full,target=rhs));prev=mod;lemmas.append(tag)
(E/'field-bridges.json').write_text(json.dumps(out,indent=2)+'\n');print(len(out))
