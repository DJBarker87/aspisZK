"""Generate one combined statement audit, one axioms audit, one focused replay."""
from pathlib import Path
import json,re,hashlib,subprocess
E=Path('evidence/pv-rj4idb-20261029');plan=json.loads((E/'build-plan.json').read_text());audit={'PV_RJ4IDB_Statements','PV_RJ4IDB_Axioms','PV_RJ4IDB_Replay'}
mods=[m for m in plan['modules'] if m not in audit];theorems=[];defs=[];freeze=[]
for m in mods:
 v=plan['modules'][m];s=subprocess.check_output(['git','show','HEAD:'+v['path']],text=True)
 if m.startswith('PV_RJ4IDB_'):
  ns=re.search(r'^namespace (\S+)',s,re.M)[1]
  theorems += [ns+'.'+n for n in re.findall(r'^theorem (\w+)',s,re.M)]
  if m=='PV_RJ4IDB_OpenInputs':defs += [ns+'.'+n for n in re.findall(r'^def (\w+)',s,re.M)]
 freeze.append(dict(module=m,path=v['path'],revision=v['revision'],source_sha256=v['sha256'],git_blob=v['git_blob']))
assert len(theorems)==len(set(theorems));assert len(defs)==9
imports=''.join('import '+m+'\n' for m in mods)
root_checks=['R1Z.PV_RJDec_CommonCases.complete_pair','R1Z.PV_RJDec_ResultCases.fibres_iff','R1Z.PV_RJDec_V047Native.consume','R1Z.PV_RJ4IDB_NativePowers.deployed_installation','R1Z.PV_RJ4IDB_CallerSemantic.caller_to_transfer13','R1Z.PV_RJ4IDB_CallerSemantic.consume','PV_RJ4IDB.native_factorization','PV_RJ4IDB.all_prefixes','PV_RJ4IDB.result_fibres_exact']
Path('lean/PV_RJ4IDB_Statements.lean').write_text(imports+'/-! Complete checked types; native producer inputs remain OPEN Props, not instances. -/\n'+''.join('#check '+n+'\n' for n in theorems+defs+root_checks))
Path('lean/PV_RJ4IDB_Axioms.lean').write_text('import PV_RJ4IDB_Statements\n'+''.join('#print axioms '+n+'\n' for n in theorems+defs+root_checks[:3]))
Path('lean/PV_RJ4IDB_Replay.lean').write_text('import PV_RJ4IDB_Axioms\n/-! Single final focused cached manifest; NOT a whole privacy release replay. -/\n'+''.join('#check '+n+'\n#print axioms '+n+'\n' for n in root_checks))
(E/'proof-source-freeze.json').write_text(json.dumps(dict(modules=freeze,new_theorem_names=theorems,open_input_definitions=defs,audit_targets={'64697':'PV_RJ4IDB_Statements','64698':'PV_RJ4IDB_Axioms','64699':'PV_RJ4IDB_Replay'},classification='focused coherent cached source/object checks; no whole deployed privacy release claim'),indent=2)+'\n')
print(len(mods),'accepted source modules,',len(theorems),'new theorem queries,',len(defs),'typed open inputs')
