"""Recompile retained emitted bodies with enum-qualified discriminant names."""
from pathlib import Path
import json,hashlib,sys
def emit(path,text):
 if '--check' in sys.argv:
  assert path.read_text()==text,('generated drift',str(path))
 else:path.write_text(text)
E=Path(__file__).resolve().parent;G=json.loads((E/'NFN_SOURCE_GRAPH.json').read_text())
mods=['NEW_GeometryActual.Types','NEW_GeometryActual.FunsExternal','NEW_GeometryActual.Funs','NEW_InverseActual.Types','NEW_InverseActual.Funs','NFB_RowRef.Types','NFB_RowRef.FunsExternal','NFB_RowRef.Funs']
imports=['Lean','NFN_PhaseTransport','ImportUnionNamedDiscriminant'];body=[];records=[]
for n in mods:
 r=G[n];src=r['source'];out=[]
 for line in src.splitlines():
  if line.startswith('import '):
   for d in line[7:].split():
    if d not in mods and d not in imports:imports.append(d)
  else:out.append(line.replace('discriminant isize','import_union_discriminant isize'))
 s='\n'.join(out)+'\n';body.append('-- BEGIN retained emitted '+n+'\nsection\n'+s+'end\n-- END '+n+'\n')
 records.append(dict(module=n,path=r['path'],sha256=hashlib.sha256(src.encode()).hexdigest(),new_body_sha256=hashlib.sha256(s.encode()).hexdigest(),changes=['imports','anonymous discriminant instance naming only','per-file option scope']))
audit='''\nrun_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
'''
emit(E/'NFN_ExtractedGeometry.lean',''.join('import '+n+'\n' for n in imports)+'\n'+''.join(body)+audit)
emit(E/'NFN_EXTRACTED_RETARGET.json',json.dumps(records,indent=1)+'\n')
assert "'NFN_ExtractedGeometry'" in (E/'NFN_generate.py').read_text()
