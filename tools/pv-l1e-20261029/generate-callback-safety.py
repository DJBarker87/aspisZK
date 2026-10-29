"""Generate symbolic callback-safety proofs over the logged model graph.
Each source body is unfolded once, and composed callees use named lemmas.
This is not a certificate of native events or unlogged opaque leaf effects.
"""
from pathlib import Path
import json,re,sys,hashlib
E=Path('evidence/pv-l1e-20261029')
order=json.loads((E/'missing-order.json').read_text())
mods=[m for m in order if m.startswith('PV_L1D_Source_') or m in ['PV_L1D_QueryAbsorb','PV_L1D_QueryProducer']]+['PV_L1E_Source_070']
code='import PV_L1E_Source_070\nimport PV_L1D_CallbackSafe\nimport PV_L1E_SafeObserve\nimport PV_L1E_SafetyTactics\nset_option autoImplicit false\nnoncomputable section\nnamespace PV_L1E_CallbackSafety\nopen Aeneas Aeneas.Std Result ControlFlow ProverRwFull\nopen PV_L1D_Logged PV_L1D_CallbackSafe\nvariable [ExternalTypes] [ExternalFuns]\n'
code+='''theorem safe_coe {α : Type} (r : Result α) : Safe (r : Logged α) := rfl
#print axioms safe_coe
'''
known=[];manifest=[]
for m in mods:
 s=Path('lean',m+'.lean').read_text();start=s.index('theorem complete_result');end=s.index(' := by',start)
 sig=s[start:end];params,claim=sig.split('  erase (produce ',1);app=claim.split(') = ',1)[0]
 params=params.replace('theorem complete_result','theorem safe_'+m)
 code+=params+'  Safe ('+m+'.produce '+app+') := by\n  unfold '+m+'.produce\n'
 code+='  try simp only [PV_L1D_Projection.prod_case]\n'
 code+="  repeat' first\n"
 code+='    | solve | l1e_safe_callee\n'
 code+='''    | with_reducible exact safe_lift _
    | with_reducible exact safe_coe _
    | with_reducible exact safe_pure _
    | l1e_safe_observe
    | with_reducible apply safe_bind
    | intro value
    | split <;> try simp only [PV_L1D_Projection.prod_case]
'''
 code+='#print axioms safe_'+m+'\n';known.append(m);manifest.append(dict(module=m,sha256=hashlib.sha256(s.encode()).hexdigest()))
code+='end PV_L1E_CallbackSafety\n'
p=Path('lean/PV_L1E_CallbackSafety.lean')
if '--check' in sys.argv:
 assert p.read_text()==code
else:p.write_text(code)
(E/'callback-safety-generator.json').write_text(json.dumps(dict(modules=manifest,output_sha256=hashlib.sha256(code.encode()).hexdigest(),checked='--check' in sys.argv),indent=2)+'\n')
print(len(mods),'symbolic proofs; bytes',len(code))
