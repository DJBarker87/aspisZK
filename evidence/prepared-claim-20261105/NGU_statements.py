from pathlib import Path
import json
E=Path(__file__).resolve().parent;P=json.loads((E/'NGU_PROVENANCE.json').read_text());A=json.loads((E/'NGU_AUDIT_ROOTS.json').read_text());roots=A['roots'];owners={}
for root in roots:
 s=root.removeprefix('AspisR1.').split('.')[0]
 if s in ['NGU_PreparedClaim','NGU_ClaimOps','NGU_Powers','NGU_Weighted','NGU_WeightedStep','NGU_ArrayRead','NGU_ArrayMap','NGU_Loop','NGU_ResultTransport']:owners[root]=s
 else:owners[root]=P['module_owner'][s.removeprefix('NGU_')]
groups=[roots[i*len(roots)//12:(i+1)*len(roots)//12] for i in range(12)]
for i,names in enumerate(groups):
 s='import Lean\nimport NGU_COMBINED_IMPORT\nopen Lean\nset_option pp.universes true\nset_option pp.explicit true\n'
 for n in names:s+=f'#check @{n}\n#print axioms {n}\n'
 s+='\nrun_cmd do\n let env ← Lean.getEnv\n'
 for n in names:
  s+=f''' let n := `{n}
 let some idx := env.getModuleIdxFor? n | throwError "missing selected theorem owner"
 unless env.header.moduleNames[idx.toNat]! == `{owners[n]} do throwError "wrong selected theorem owner"
 let some ci := env.find? n | throwError "missing theorem constant"
 unless ci.isTheorem do throwError "selected constant is not a theorem"
 let entry := Json.mkObj [("name",toJson n.toString),("owner",toJson env.header.moduleNames[idx.toNat]!.toString),("type",toJson (reprStr ci.type))]
 logInfo m!"NGU_CERT_ENTRY {{entry.compress}}"
'''
 (E/f'NGU_Statements{i:02}.lean').write_text(s)
(E/'NGU_STATEMENT_ROOTS.json').write_text(json.dumps(dict(groups=groups,owners=owners,selection='All366 printed new own theorem roots, expected owners derived from original source mapping rather than loaded lookup.'),indent=1)+'\n')
