from pathlib import Path
import json,re,difflib,hashlib
E=Path(__file__).resolve().parent
roots=set()
for p in E.glob('NFE_L*/receipt.json'):
 r=json.loads(p.read_text())
 if r['kind']=='lean' and r['exit_status']==0:
  for l in r['print_axioms']:roots.add(re.search("'([^']+)'",l)[1])
roots.add('AspisR1.RPx_Deployed.deployed')
# Final root addition is recorded before compiling the driver; stable 41 bounded groups.
groups=[[] for _ in range(41)]
for i,n in enumerate(sorted(roots)):groups[i%41].append(n)
original=(E.parent/'axaudit2-20261102/NEP_Driver.lean').read_text()
s=original.replace('import NEP_WALKER','import NFA_WALKER\nimport NFA_MemoryLimit')
s=s.replace('  enableInitializersExecution','  NFA_MemoryLimit.set\n  initSearchPath (← findSysroot)\n  enableInitializersExecution',1)
a=s.index('  let (modules, roots) :=');b=s.index('  let env ←',a)
selection='  let (modules, roots) :=\n'
for i,g in enumerate(groups):
 selection+=('    if' if i==0 else '    else if')+' mode == "proof'+str(i)+'" then\n      (#[`NFE_CombinedFinal], #['+', '.join('`'+n for n in g)+'])\n'
selection+='    else if mode == "scan" then (#[`NFE_CombinedFinal], #[])\n    else if mode == "fixtures" then\n      (#[`NEP_Planted, `NEP_Mutations],\n       #[`NEP_Planted.matcher, `NEP_Planted.viaPrivate, `NEP_Planted.proof,\n         `NEP_Planted.viaAux, `NEP_MutateMatch.matcher, `NEP_MutatePrivate.viaPrivate,\n         `NEP_MutateProof.proof, `NEP_MutateAux.viaAux])\n    else (#[], #[])\n'
s=s[:a]+selection+s[b:]
# Exact NER active-declaration scanner (no walker edits), integrated in the same environment.
ner=(E.parent/'coherent-20261102/NER_FinalDriverV2.lean').read_text()
start=ner.index('namespace NER');end=ner.index('\nopen Lean Elab Command',start)
scanner=ner[start:end]
s=s.replace('open Lean Elab Command','open Lean Elab Command\n'+scanner,1)
point='  let ctx : Command.Context := {'
scan='''  if mode == "scan" then
    let mut expected : Std.HashMap String (Array String) := {}
    for line in ← IO.FS.lines "NFE_EXPECTED_IMPORTS.jsonl" do
      let j ← IO.ofExcept (Json.parse line)
      expected := expected.insert (← IO.ofExcept (j.getObjValAs? String "module"))
        (← IO.ofExcept (j.getObjValAs? (Array String) "imports"))
    let failed ← NER.loadedScan env "NFE_LOADED_scan.jsonl" expected
    IO.println (if failed then "NFE_SCAN_FAILED" else "NFE_SCAN_ZERO_DANGLING")
    return if failed then 1 else 0
'''
s=s.replace(point,scan+point,1)
(E/'NFE_Driver.lean').write_text(s)
(E/'NFE_DRIVER.diff').write_text(''.join(difflib.unified_diff(original.splitlines(True),s.splitlines(True),fromfile='NEP_Driver.lean',tofile='NFE_Driver.lean')))
(E/'NFE_DRIVER_ROOTS.json').write_text(json.dumps(dict(roots=sorted(roots),groups=groups,walker_sha256=hashlib.sha256((E.parent/'axaudit2-20261102/NEP_WALKER.lean').read_bytes()).hexdigest(),scanner_source='evidence/coherent-20261102/NER_FinalDriverV2.lean',scanner_sha256=hashlib.sha256(scanner.encode()).hexdigest()),indent=2)+'\n')
print(len(roots),'roots in41 groups')
