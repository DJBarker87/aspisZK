from pathlib import Path
import json,re
L=Path('evidence/pv-lib-20261107/lane-SPEC')
modules={'w3':[], 'w4':[]}
for f in sorted(L.glob('receipt-497*.json')):
 r=json.loads(f.read_text());a=r['attempt'];m=r.get('target','')
 if a>=49737 and a<=49779 and r.get('accepted') and m.startswith('PV_LIB_SPEC_') and m!='PV_LIB_SPEC_CohortImports':
  c=r['cohort']
  if m not in modules[c]:modules[c].append(m)
base=Path('lean/PV_LIB_SPEC_RawAuditSession4.lean').read_text()
# Retain NEP.audit and collectAxioms unchanged. Summary union extends to every
# reached constructor (kernel declarations), not an axiom whitelist.
base=base.replace('for aux in #[`PV_THR2_OwnInitExactReturnedCases.Cases.mk, `PV_FN_THREAD_f361.Pre.mk] do', '''let importedEnv := (← getEnv).setExporting false
        let constructors := importedEnv.constants.toList.filterMap fun (n, info) =>
          match info with
          | .ctorInfo _ => if reached.contains n.toString then some n else none
          | _ => none
        for aux in constructors do''')
manifest={}
for cohort,ms in modules.items():
 roots=[]
 for m in ms:
  stack=[]
  for line in Path('lean',m+'.lean').read_text().splitlines():
   ns=re.match(r'^namespace\s+(\S+)',line)
   end=re.match(r'^end\s+(\S+)',line)
   dec=re.match(r'^(?:noncomputable\s+)?(?:def|abbrev|structure|inductive|theorem)\s+([\w\'.]+)',line)
   if ns:stack.append(ns[1])
   elif end:
    assert stack and stack[-1]==end[1],(m,stack,line)
    stack.pop()
   elif dec:
    root='.'.join(stack+[dec[1]])
    if root not in roots:roots.append(root)
  assert not stack,(m,stack)
 a=base.index('  let (modules, roots) :=');b=base.index('  let env ← importModules',a)
 s=base[:a]+'  let (modules, roots) :=\n    (#['+', '.join('`'+m for m in ms)+'],\n     #['+', '.join('`'+r for r in roots)+'])\n'+base[b:]
 name='PV_LIB_SPEC_RawAuditSession5'+cohort.upper()
 Path('lean',name+'.lean').write_text(s)
 manifest[cohort]={'driver':name,'modules':ms,'roots':roots,'count':len(roots)}
(L/'SESSION5_RAW_ROOTS.json').write_text(json.dumps(manifest,indent=2)+'\n')
print({c:(len(v['modules']),v['count']) for c,v in manifest.items()})
