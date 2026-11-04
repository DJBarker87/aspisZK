"""Deterministic import-only retarget, copied proofs with complete provenance."""
from pathlib import Path
import json,hashlib,functools,re,sys
def emit(path,text):
 if '--check' in sys.argv:
  assert path.read_text()==text,('generated drift',str(path))
 else:path.write_text(text)
E=Path(__file__).resolve().parent
G=json.loads((E/'NFN_SOURCE_GRAPH.json').read_text())
@functools.lru_cache(None)
def affected(n):
 return n in {'FIo_NativeTypes','NEW_LoopMap','NEW_ResultMapSyntax','NEW_ShiftAssociation'} or any(affected(x) for x in G.get(n,{}).get('imports',[]))
order=[];seen=set()
def visit(n):
 if n in seen or not affected(n):return
 seen.add(n)
 if n!='FIo_NativeTypes':
  for x in G[n].get('imports',[]):visit(x)
 order.append(n)
for root in ['NFB_GeometryInstall','NFB_GeometryComposed']:visit(root)
# Keep emitted/carrier names intact; retarget every proof namespace to NFN.
rename={n:'NFN_'+n for n in order if n.startswith(('NFB_','NEW_','NEB_','NEA_','NET_','NEO_','NBG_','NBS_','LPf_','LPi_'))}
pattern=re.compile(r'(?<![A-Za-z0-9_])('+'|'.join(map(re.escape,sorted(rename,key=len,reverse=True)))+r')(?![A-Za-z0-9_])')
# A batch is one new source module, with all earlier imported file boundaries
# retained as comments. No Lean/package build runs here.
groups=[];current=[];lines=0
for n in order:
 size=len(G[n]['source'].splitlines())
 if current and (lines+size>850 or n=='NFB_GeometryComposed'):
  groups.append(current);current=[];lines=0
 current.append(n);lines+=size
if current:groups.append(current)
owner={n:f'NFN_GeometryPart{i:02}' for i,ns in enumerate(groups) for n in ns}
reuse={n:'RPz7_'+n for n in ['FIo_NativeTypes','FIo_NativeExternal','FIo_NativeFuns']}
owner.update(reuse)
records=[]
for i,names in enumerate(groups):
 module=f'NFN_GeometryPart{i:02}';imports=['Lean','NFN_PhaseTransport','NFN_ReserveOwner'];bodies=[]
 for n in names:
  if n in reuse:
   if reuse[n] not in imports:imports.append(reuse[n])
   continue
  r=G[n];src=r['source'];body=[]
  for line in src.splitlines():
   if line.startswith('import '):
    for d in line[7:].split():
     if n=='FIo_NativeTypes' and d=='NP6_StdModel':continue
     mapped=owner.get(d,{'FIo_ReduceBounds':'RPt_FIo_ReduceBounds','JFv_RawExtractedSemanticCallOpsV20':'RPu_JFv_RawExtractedSemanticCallOpsV20',**{m:'NFN_ExtractedGeometry' for m in ['NEW_GeometryActual.Types', 'NEW_GeometryActual.FunsExternal', 'NEW_GeometryActual.Funs', 'NEW_InverseActual.Types', 'NEW_InverseActual.Funs', 'NFB_RowRef.Types', 'NFB_RowRef.FunsExternal', 'NFB_RowRef.Funs']}}.get(d,d))
     if mapped!=module and mapped not in imports:imports.append(mapped)
   else:body.append(line)
  text='\n'.join(body)+'\n'
  if n=='FIo_NativeTypes':text=text.replace('AspisR1.NP6_StdModel.ReserveError','NFN_ReserveOwner.ReserveError')
  if n=='NEW_GeometryArithmetic':
   text=text.replace('NEW_InverseActual.aspis_core.field.square_n_loop.body,multiply,NEW_InverseAssociation.multiply]\n  rfl','NEW_InverseActual.aspis_core.field.square_n_loop.body,multiply,NEW_InverseAssociation.multiply] <;> rfl')
  text=pattern.sub(lambda m:rename[m.group()],text)
  text=text.replace('NFB_RowRef.NFN_NFB_RowLog','NFB_RowRef.NFB_RowLog')
  bodies.append(f'-- BEGIN copied {n}: {r["path"]}\n'+text+f'-- END copied {n}\n')
  records.append(dict(original_module=n,original_path=r['path'],original_sha256=hashlib.sha256(src.encode()).hexdigest(),target_module=module,transformed_body_sha256=hashlib.sha256(text.encode()).hexdigest(),namespace_map_sha256=hashlib.sha256(json.dumps(rename,sort_keys=True).encode()).hexdigest(),changes=['imports','proof namespace names']+(['compose already-solving simp with rfl using <;>'] if n=='NEW_GeometryArithmetic' else [])))
 # Ask Lean for every theorem created in this module, including private lemmas.
 audit='''\nrun_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
'''
 emit(E/(module+'.lean'),''.join('import '+m+'\n' for m in imports)+'\n'+''.join(bodies)+audit)
emit(E/'NFN_RETARGET_PROVENANCE.json',json.dumps(dict(order=order,groups=groups,module_owner=owner,proof_namespace_map=rename,files=records),indent=1)+'\n')
print('copied',len(order),'modules into',len(groups),'NFN source modules')
