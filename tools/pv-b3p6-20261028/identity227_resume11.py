"""Emit complete lexical-body identities, one body/module, via named theorem.
These establish identity under a COMMON interpretation of callees; import/type
retargeting and the connection of that interpretation to each extracted model
are separate obligations. Never count these alone as an op227 callback proof.
"""
from pathlib import Path
import json,sys,hashlib
D=Path('evidence/pv-b3p6-20261028');O=D/'resume11';L=D/'lean'
inv=json.loads((D/'resume9/body-inventory.json').read_text());reach=json.loads((O/'reachability.json').read_text());files={};records=[]
header='namespace PV_B3P_Binding11227\nset_option autoImplicit false\n'
files['PV_B3P_BodyIdentity11227']='import Aeneas.Std\n'+header+'''/-- Equal complete token bodies have equal interpretations, including all Result tags.
The caller must supply the SAME interpretation of imports, macros and constants. -/
theorem token_identity11 (body : String) : body = body := Eq.refl body
theorem interpret_identity11 {α : Sort _} (interpret : String → α)
    (source owned : String) (binding : source = owned) : interpret source = interpret owned :=
  congrArg interpret binding
#print axioms token_identity11
#print axioms interpret_identity11
end PV_B3P_Binding11227
'''
for r in reach['bodies']:
 if r['classification']!='reachable-conservative' or r['status']!='identical':continue
 b=inv['bodies'][r['inventory_index']];assert b['source']['tokens']==b['owned']['tokens']
 n=f'{r["family"]}_{r["key"].replace("#","_")}';mod='PV_B3P_Identity11'+f'{len(records):02}'+'227';literal=json.dumps(json.dumps(b['source']['tokens'],ensure_ascii=False,separators=(',',':')),ensure_ascii=False)
 s='import PV_B3P_BodyIdentity11227\n'+header
 s+=f'/-- {r["family"]}/{r["key"]}; complete source and owned lexical token sequences. -/\ndef source_tokens11_{n} : String := {literal}\ndef owned_tokens11_{n} : String := {literal}\n'
 s+=f'theorem body_identity11_{n} : source_tokens11_{n} = owned_tokens11_{n} :=\n  token_identity11 source_tokens11_{n}\n'
 s+=f'theorem body_interpretation11_{n} {{α : Sort _}} (interpret : String → α) :\n    interpret source_tokens11_{n} = interpret owned_tokens11_{n} :=\n  interpret_identity11 interpret _ _ body_identity11_{n}\n'
 s+=f'#print axioms body_identity11_{n}\n#print axioms body_interpretation11_{n}\nend PV_B3P_Binding11227\n';files[mod]=s
 records.append(dict(inventory_index=r['inventory_index'],family=r['family'],key=r['key'],module=mod,theorem='PV_B3P_Binding11227.body_identity11_'+n,interpretation_theorem='PV_B3P_Binding11227.body_interpretation11_'+n,source_sha256=b['source']['sha256'],owned_sha256=b['owned']['sha256'],token_count=len(b['source']['tokens']),scope='complete lexical body identity under COMMON callee/import/macro/constant interpretation; extracted-model association not supplied by this theorem'))
for m,s in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==s,m
 else:p.write_text(s)
x=dict(modules=list(files),bodies=records,count=len(records),semantic_use='reclassification within existing Charon/Aeneas tool trust',not_claimed='No theorem interprets a token String as the actual Rust or Aeneas semantics; source-to-extraction association is separate. No callee retargeting, D188 or own-1 dependency closure is discharged by a common-interpretation identity.')
p=O/'identity-bindings.json'
if '--check'in sys.argv:assert json.loads(p.read_text())==x
else:p.write_text(json.dumps(x,indent=2)+'\n')
print(len(records))
