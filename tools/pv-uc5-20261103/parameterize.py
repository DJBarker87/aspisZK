from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-uc5-20261103';I=E/'entry-extraction';O=R/'tools/pv-uc5-20261103/lean/PVUC5Entry';O.mkdir(exist_ok=True)
ns='PV_UC5_Entry';rows=[]
for kind in ['Types','Funs']:
 raw=(I/(kind+'External_Template.lean')).read_text()
 declarations=re.findall(r'(?m)^axiom\s+(\S+)([\s\S]*?)(?=\n\n|\Z)',raw)
 fields=['  op'+str(i)+rest for i,(name,rest) in enumerate(declarations)]
 header='import Aeneas\n'+('import PVUC5Entry.Types\nimport PVUC5Entry.FloatCarrier\nimport PVUC5Entry.NativeConstants\n' if kind=='Funs' else '')+'open Aeneas Aeneas.Std Result ControlFlow Error\nnamespace '+ns+'\n\n'
 cls='External'+kind;s=header+'class '+cls+(' [ExternalTypes]' if kind=='Funs' else '')+' where\n'+'\n'.join(fields)+'\n\n'
 for i,(name,rest) in enumerate(declarations):
  binders='[types : ExternalTypes] [ext : ExternalFuns]' if kind=='Funs' else '[ext : ExternalTypes]';args='types ext' if kind=='Funs' else 'ext'
  s+='abbrev '+name+' '+binders+' := @'+cls+'.op'+str(i)+' '+args+'\n';rows.append(dict(kind=kind,index=i,name=name,signature=rest))
 s+='end '+ns+'\n';(O/(kind+'External.lean')).write_text(s)
# Proof-only literal certificates. Computational calls and literals unchanged.
pattern=r'\btoStr\s+("(?:[^"\\]|\\.)*")'
source=(I/'Funs.lean').read_text();literals=list(dict.fromkeys(json.loads(m[1]) for m in re.finditer(pattern,source)))
B=O/'LiteralBounds.lean'
b='import Aeneas\nimport PV_UC5_LiteralBounds\nopen Aeneas Aeneas.Std\nnamespace PV_UC5_Literals\n'
for i,lit in enumerate(literals):
 assert lit.isascii() and len(lit)<64
 chars='['+', '.join("'"+c+"'" for c in lit)+']'
 b+=f'theorem size_{i} : {json.dumps(lit)}.toByteArray.size = {len(lit)} := by\n  change (String.ofList {chars}).toByteArray.size = {len(lit)}\n  rfl\n'
 b+=f'theorem bound_{i} : {json.dumps(lit)}.toByteArray.size ≤ U32.max :=\n  PV_UC5_LiteralBounds.short_bound _ _ size_{i} (by omega)\n#print axioms size_{i}\n#print axioms bound_{i}\n'
b+='end PV_UC5_Literals\n';B.write_text(b)
for kind in ['Types','Funs']:
 raw=(I/(kind+'.lean')).read_text();s=raw.replace('PVUCEntryUc5.','PVUC5Entry.').replace('namespace PV_UC_Entry\n','namespace '+ns+'\nvariable [ExternalTypes]'+(' [ExternalFuns]' if kind=='Funs' else '')+'\n').replace('end PV_UC_Entry\n','end '+ns+'\n')
 # Aeneas determines imports from file stem; keep exact inverse check below.
 original=s
 restored=original.replace('PVUC5Entry.','PVUCEntryUc5.').replace('namespace '+ns+'\nvariable [ExternalTypes]'+(' [ExternalFuns]' if kind=='Funs' else '')+'\n','namespace PV_UC_Entry\n').replace('end '+ns+'\n','end PV_UC_Entry\n')
 assert restored==raw
 replacements=[]
 if kind=='Funs':
  def repl(m):
   lit=json.loads(m[1]);replacement=m[0]+' PV_UC5_Literals.bound_'+str(literals.index(lit));replacements.append((replacement,m[0]));return replacement
  s=re.sub(pattern,repl,s)
  s=s.replace('import Aeneas\n','import Aeneas\nimport PVUC5Entry.LiteralBounds\n')
  s=s.replace('variable [ExternalTypes] [ExternalFuns]\n','variable [ExternalTypes] [ExternalFuns]\nattribute [local irreducible] toStr\n')
  inverse=s.replace('import PVUC5Entry.LiteralBounds\n','').replace('attribute [local irreducible] toStr\n','')
  for a,z in replacements:inverse=inverse.replace(a,z)
  assert inverse==original
 (O/(kind+'.lean')).write_text(s)
for name in ['FloatCarrier','NativeConstants']:
 s=(R/'tools/pv-uc-20261029/lean/PVUCReadyEntry'/(name+'.lean')).read_text().replace('PV_UC_ReadyEntry',ns).replace('PVUCReadyEntry.','PVUC5Entry.');(O/(name+'.lean')).write_text(s)
(E/'parameterization.json').write_text(json.dumps(dict(computational_edits=False,proof_only_inverse_check=True,literal_sites=len(replacements),distinct_literals=literals,external_parameters=rows,status='parametric envelope; native instances remain obligations'),indent=2)+'\n')
print((O/'Types.lean').read_text()[:250]);print(len(replacements),len(literals))
