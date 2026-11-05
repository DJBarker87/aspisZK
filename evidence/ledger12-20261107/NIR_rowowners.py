from pathlib import Path
import sys,json,lzma,re,subprocess
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1]
def J(path):
 p=R/path;raw=p.read_bytes()if p.exists()else subprocess.check_output(['git','show','HEAD:'+path]);return json.loads(lzma.decompress(raw)if path.endswith('.xz')else raw)
# Exact established retarget maps, not guessed renaming.
mp={}
for path,key in [('evidence/slice-q-phase-20261104/NFN_RETARGET_PROVENANCE.json','proof_namespace_map'),('evidence/slice-q-accum-20261104/NFS_RETARGET_PROVENANCE.json','namespace_map')]:mp.update(J(path)[key])
(E/'NIR_NAMESPACE_MAP.json').write_text(json.dumps(mp,indent=1)+'\n')
b=J('evidence/ledger11-20261107/NII_LEDGER.json.xz');old=J('evidence/ledger12-20261107/NIR_LEDGER.json.xz');missing=set(J('evidence/ledger12-20261107/NIR_OWNER_CHECK.json')['missing_closed_roots']);candidates=set()
for row in old['rows']:
 if row['row']not in missing:continue
 cert=row['obligation']['certificate']
 def walk(v):
  if isinstance(v,str):
   for token in re.findall(r'(?<![\w.])[A-Za-z_][\w]*(?:\.[A-Za-z_][\w]*)+',v):
    bits=token.split('.');off=1 if bits[0]=='AspisR1'else 0
    if bits[off]in mp:
     bits[off]=mp[bits[off]];n='.'.join(bits);candidates.add(n);candidates.add('AspisR1.'+n if off==0 else n)
  elif isinstance(v,dict):
   for x in v.values():walk(x)
  elif isinstance(v,list):
   for x in v:walk(x)
 walk(cert)
# Source-backed candidates only; imports and nonexistent old spellings are reported explicitly.
(E/'NIR_ROW_CANDIDATES.json').write_text(json.dumps(sorted(candidates),indent=1)+'\n')
s='''import NIR_COMBINED_IMPORT
import Lean
open Lean Elab Command
set_option pp.all true
run_cmd do
  let env ← getEnv
  for root in (#['''+','.join('"'+n+'"'for n in sorted(candidates))+'''] : Array String) do
    let declName := root.toName
    match env.find? declName, env.getModuleIdxFor? declName with
    | some c, some idx =>
      let statement ← liftTermElabM (PrettyPrinter.ppExpr c.type)
      logInfo m!"NIR_OWNER {(Json.mkObj [("root",toJson root),("owner_module",toJson env.header.moduleNames[idx]!.toString),("obligation_statement",toJson statement.pretty)]).compress}"
    | _, _ => logInfo m!"NIR_ABSENT {root}"
'''
(E/'NIR_RowOwnerStatements.lean').write_text(s);print('NIR row-owner candidates',len(candidates))
