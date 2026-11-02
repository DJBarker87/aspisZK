"""Expose extraction holes as explicit class parameters, never as axioms.

This is a parametric compilation envelope, NOT native instantiation or privacy
credit. It follows the existing ProverRwFull ExternalTypes/ExternalFuns scheme.
The raw emitted body is retained verbatim modulo namespace and binder/import
lines; no model function body, operation, branch or builtin is replaced.
"""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-uc-20261029';I=E/'entry-extraction-d561';O=R/'tools/pv-uc-20261029/lean/PVUCEntryParam';O.mkdir(exist_ok=True)
ns='PV_UC_EntryParam';sha=lambda s:hashlib.sha256(s.encode()).hexdigest();rows=[]
for kind,count in [('Types',25),('Funs',119)]:
 s=(I/(kind+'External_Template.lean')).read_text()
 declarations=re.findall(r'(?m)^axiom\s+(\S+)([\s\S]*?)(?=\n\n|\Z)',s)
 assert len(declarations)==count,(kind,len(declarations))
 # Every abstract operation retains its exact original type and binders.
 fields=['  op'+str(i)+rest for i,(name,rest) in enumerate(declarations)]
 header='import Aeneas\n'+('import PVUCEntryParam.Types\n' if kind=='Funs' else '')+'open Aeneas Aeneas.Std Result ControlFlow Error\nnamespace '+ns+'\n\n'
 cls='External'+kind
 text=header+'class '+cls+(' [ExternalTypes]' if kind=='Funs' else '')+' where\n'+'\n'.join(fields)+'\n\n'
 for i,(name,rest) in enumerate(declarations):
  binders='[types : ExternalTypes] [ext : ExternalFuns]' if kind=='Funs' else '[ext : ExternalTypes]'
  args='types ext' if kind=='Funs' else 'ext'
  text+='abbrev '+name+' '+binders+' := @'+cls+'.op'+str(i)+' '+args+'\n'
  rows.append(dict(kind=kind,index=i,name=name,original_signature=rest,signature_sha256=sha(rest)))
 text+='\nend '+ns+'\n';(O/(kind+'External.lean')).write_text(text)
for kind in ['Types','Funs']:
 raw=(I/(kind+'.lean')).read_text();s=raw.replace('PVUCEntry.','PVUCEntryParam.').replace('namespace PV_UC_Entry\n','namespace '+ns+'\nvariable [ExternalTypes]'+(' [ExternalFuns]' if kind=='Funs' else '')+'\n').replace('end PV_UC_Entry\n','end '+ns+'\n')
 # Mechanical inverse checks: no emitted function/structure body edits.
 restored=s.replace('PVUCEntryParam.','PVUCEntry.').replace('namespace '+ns+'\nvariable [ExternalTypes]'+(' [ExternalFuns]' if kind=='Funs' else '')+'\n','namespace PV_UC_Entry\n').replace('end '+ns+'\n','end PV_UC_Entry\n')
 assert restored==raw
 (O/(kind+'.lean')).write_text(s)
assert not any(re.search(r'\b(?:axiom|sorry|admit|native_decide)\b',p.read_text()) for p in O.glob('*.lean'))
(E/'entry-parameterization-d561.json').write_text(json.dumps(dict(status='PARAMETRIC ENVELOPE ONLY; faithful native instance not supplied',source_templates={p.name:sha(p.read_text()) for p in I.glob('*.lean')},outputs={p.name:sha(p.read_text()) for p in O.glob('*.lean')},inverse_body_check=True,external_type_parameters=25,external_function_parameters=119,rows=rows,limitations=['All original external obligations remain explicit class parameters, not global axioms or discharged P obligations.','Aeneas builtin fmt and stdio semantics are unchanged and receive no privacy credit.','Pure public-argument renderers are handled separately; neither private recovery data nor elapsed timing is declared public by this envelope.']),indent=2)+'\n')
