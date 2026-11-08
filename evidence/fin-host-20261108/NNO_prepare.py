from pathlib import Path
import json,re,subprocess
E=Path(__file__).resolve().parent;R=E.parent
rows={x['module']:x for x in map(json.loads,(R/'ledger29-20261111/NNM_EXPECTED_IMPORTS.jsonl').read_text().splitlines())}
sourcepins=[]
for folder in ['stage-wrap-20261111','entry-rsl-20261111','root0-weak-20261111','top-assembly-20261107']:
 prefix='evidence/'+folder+'/'
 files=subprocess.check_output(['git','ls-tree','-r','--name-only','953e3af13bb','--',prefix],text=True).splitlines()
 for f in files:
  if not f.endswith('.lean')or'/'in f[len(prefix):]:continue
  s=subprocess.check_output(['git','show','953e3af13bb:'+f],text=True);m=Path(f).stem
  if m not in rows:
   imports=list(dict.fromkeys(([]if re.search(r'^prelude\s*$',s,re.M)else['Init'])+re.findall(r'^import ([\w.]+)',s,re.M)))
   rows[m]=dict(module=m,imports=imports);sourcepins.append(dict(module=m,path=f,revision='953e3af13bb',sha256=__import__('hashlib').sha256(s.encode()).hexdigest()))
for folder,glob in [('nvr-20261108','NVR_*.lean'),('fin-20261108','FIN_*.lean'),('fin-host-20261108','NNO_*.lean')]:
 for f in (R/folder).glob(glob):
  s=f.read_text();rows[f.stem]=dict(module=f.stem,imports=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',s,re.M))))
(E/'NNO_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(rows[k])+'\n'for k in sorted(rows)))
(E/'NNO_EXTRA_IMPORT_SOURCES.json').write_text(json.dumps(sourcepins,indent=1)+'\n')
roots=['FIN_'+str(n)+'.candidate'for n in[240,221,213,333,330]]
(E/'NNO_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots]),indent=1)+'\n')
(E/'NNO_AUDIT_MODULES.json').write_text(json.dumps([['NNO_StatementChecks']],indent=1)+'\n')
# Same fully printed statement export as NNM_Statements, with only our new roots.
f=E/'NNO_StatementChecks.lean';s=f.read_text()
if 'NNO_OWNER'not in s:
 s+='''\nopen Lean Elab Command
set_option pp.all true
run_cmd do
 let env := (← getEnv).setExporting false
 for (name, c) in env.constants.toList do
  if name.toString.startsWith "NVR_" && c.isTheorem then
   let some idx := env.getModuleIdxFor? name | throwError "missing owner {name}"
   let statement ← liftTermElabM (PrettyPrinter.ppExpr c.type)
   let row := Json.mkObj [("root",toJson name.toString),("owner_module",toJson env.header.moduleNames[idx]!.toString),("obligation_statement",toJson statement.pretty)]
   logInfo m!"NNO_OWNER {row.compress}"
'''
 f.write_text(s)
print('prepared',len(rows),'expected modules')
