from pathlib import Path
import json
E=Path(__file__).resolve().parent;P=json.loads((E/'NGU_PROVENANCE.json').read_text());A=json.loads((E/'NGU_AUDIT_ROOTS.json').read_text());roots=A['roots'];owners={}
for root in roots:
 s=root.removeprefix('AspisR1.').split('.')[0]
 if s in ['NGU_PreparedClaim','NGU_ClaimOps','NGU_Powers','NGU_Weighted','NGU_WeightedStep','NGU_ArrayRead','NGU_ArrayMap','NGU_Loop','NGU_ResultTransport']:owners[root]=s
 else:owners[root]=P['module_owner'][s.removeprefix('NGU_')]
# Compiler-generated proof auxiliaries are owned by the module which first
# synthesizes them. The focused successful receipt's final run_cmd lists only
# current-module declarations. Do not derive owners from the candidate scan.
import re
first={}
for line in (E/'NGU_ATTEMPTS.jsonl').read_text().splitlines():
 r=json.loads(line)
 if r['kind']!='lean' or r['exit_status']!=0 or r['module'].startswith('NGU_Statements'):continue
 for line in r['print_axioms']:
  m=re.match(r"'([^']+)'",line)
  if m and m[1] in roots:first.setdefault(m[1],dict(module=r['module'],receipt=r['attempt']+'/receipt.json'))
aux={n:first[n] for n in roots if any(x in n for x in ['._proof_','._simp_','.eq_'])}
for n,r in aux.items():owners[n]=r['module']
old=[roots[i*len(roots)//11:(i+1)*len(roots)//11] for i in range(11)]
indexed=[(0,old[0]),(1,old[1]),(2,old[2]+old[3]+old[4])]+[(i,old[i]) for i in range(5,11)]
groups=[ns for _,ns in indexed]
for i,names in indexed:
 s='import Lean\nimport NGU_COMBINED_IMPORT\nopen Lean\nset_option pp.universes true\nset_option pp.explicit true\n'
 for n in names:s+=f'#check @{n}\n#print axioms {n}\n'
 if i<2:s+='\nrun_cmd do\n let env ← Lean.getEnv\n'
 for n in names:
  if i>=2:s+='\nrun_cmd do\n let env ← Lean.getEnv\n'
  s+=f''' let n := `{n}
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `{owners[n]} do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {{entry.compress}}"
'''
 (E/f'NGU_Statements{i:02}.lean').write_text(s)
(E/'NGU_STATEMENT_ROOTS.json').write_text(json.dumps(dict(groups=groups,modules=[f'NGU_Statements{i:02}' for i,_ in indexed],owners=owners,auxiliary_owner_provenance=aux,selection='All366 printed new own theorem roots, expected owners derived from original source mapping rather than loaded lookup.'),indent=1)+'\n')
