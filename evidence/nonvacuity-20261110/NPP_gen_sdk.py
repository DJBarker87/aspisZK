#!/usr/bin/env python3
"""NPP_: generate NPP_ComputableSdk.lean (stage A) and NPP_SdkNovEq inputs from the NPO_ receipts.
Usage: python3 -I NPP_gen_sdk.py <repo-evidence-dir> <out-dir>
cand  = NPO_ID_DEPENDENTS.json dependents (id-dependent, intrinsic) ∪ the noncomputable closure of
        AspisR1.NOC_Run5bCtx.sdk (NPO_L035), minus Classical.*;
leaves = the 12 propDecidable leaves of that closure; idDep = the id-dependents."""
import json, sys, os
ev, out = sys.argv[1], sys.argv[2]
dep = json.load(open(os.path.join(ev, 'host-ids-20261110/NPO_ID_DEPENDENTS.json')))['dependents']
nc = json.load(open(os.path.join(ev, 'host-ids-20261110/NPO_L035/NPO_NONCOMPUTABLE.json')))
rows = {r['n']: r for r in nc['constants']}
root = 'AspisR1.NOC_Run5bCtx.sdk'
seen, st = [], [root]
while st:
    n = st.pop()
    if n in seen or n not in rows: continue
    seen.append(n); st += rows[n]['noncomputable_deps']
closure = [n for n in seen if not n.startswith('Classical.')]
leaves = [n for n in closure if rows[n]['cause'] == 'classical']
iddep = sorted(d['name'] for d in dep)
cand = sorted(set(iddep) | set(closure))
assert len(leaves) == 12, leaves
json.dump({'root': root, 'closure': closure, 'leaves': leaves, 'iddep_count': len(iddep), 'cand_count': len(cand)},
          open(os.path.join(out, 'NPP_SDK_INPUTS.json'), 'w'), indent=1)
def arr(xs): return '#[' + ',\n  '.join('`' + x if all(c.isalnum() or c in '._' for c in x) else '`«' + x + '»' for x in xs) + ']'
def lit(xs): return '#[' + ',\n  '.join(json.dumps(x) for x in xs) + ']'
lib = open(os.path.join(out, 'NPP_src/NPP_Lib.lean')).read().replace('import Lean\n', '')
names = f'''
namespace NPP.Inputs
def cand : Array String := {lit(cand)}
def leaves : Array String := {lit(leaves)}
def idDep : Array String := {lit(iddep)}
def toSet (xs : Array String) : NameSet := xs.foldl (fun s x => s.insert x.toName) {{}}
def ids : Std.HashMap Name Name := Std.HashMap.ofList [
  (`AspisR1.CPH_Program.verifier, `NPO_DeployedIds.verifierNov),
  (`NHJ_IdPacket.poolDefault, `NPO_DeployedIds.poolNov),
  (`NHJ_IdPacket.registryDefault, `NPO_DeployedIds.registryNov)]
end NPP.Inputs
'''
open(os.path.join(out, 'NPP_src/NPP_Inputs.inc'), 'w').write(names)
hdr = '''import Lean
import NOC_Run5bHost
import NPO_DeployedIds
set_option autoImplicit false
set_option maxHeartbeats 0
'''
body = '''
open Lean Meta in
run_meta do
  let (copied, eqs) ← NPP.stageA `AspisR1.NOC_Run5bCtx.sdk (NPP.Inputs.toSet NPP.Inputs.cand)
    (NPP.Inputs.toSet NPP.Inputs.leaves) NPP.Inputs.ids (NPP.Inputs.toSet NPP.Inputs.idDep) `NPP_C
  NPP.log <| Json.mkObj [("event","stageA"),("copied", toJson copied.size),("eqs", toJson (eqs.map toString))]
  for e in eqs do
    let ax ← collectAxioms e
    NPP.log <| Json.mkObj [("axioms", toJson e.toString), ("value", toJson (ax.map toString))]
  for c in copied do
    NPP.log <| Json.mkObj [("copy", toJson c.toString), ("noncomputable", toJson (isNoncomputable (← getEnv) c)),
      ("ir", toJson ((Lean.IR.findEnvDecl (← getEnv) c).isSome))]
'''
derive = open(os.path.join(out, 'NPP_src/NPP_Derive.inc')).read()
open(os.path.join(out, 'NPP_src/NPP_ComputableSdk.lean'), 'w').write(hdr + lib + names + derive + body)
novmain = open(os.path.join(out, 'NPP_src/NPP_NovMain.inc')).read()
open(os.path.join(out, 'NPP_src/NPP_SdkNovTool.lean'), 'w').write('import Lean\nset_option autoImplicit false\n' + lib + names + novmain)
print(len(cand), len(leaves), len(iddep), len(closure))
