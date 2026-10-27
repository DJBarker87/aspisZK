#!/usr/bin/env python3
"""Generate three disjoint axiom-report shards for one full PV_Src audit."""
import pathlib,re,json,hashlib
root=pathlib.Path(__file__).resolve().parents[2];lean=root/'docs/research/v8-r0-zk-20261009/lean/R1Z';e=root/'evidence/pv-srcid3-20261026'
sources={p.stem:p for p in lean.glob('PV_Src_*.lean') if not p.stem.startswith('PV_Src_FinalAudit') and p.stem!='PV_Src_CacheInventory'}
checks=set();rows=[]
for name,p in sorted(sources.items()):
 s=p.read_text();ns=re.findall(r'^namespace (\S+)',s,re.M);theorems=re.findall(r'^[ \t]*(?:@\[[^\n]*\]\s*)?(?:theorem|lemma)\s+(\S+)',s,re.M)
 assert not theorems or len(ns)==1,(name,ns)
 names=[ns[0]+'.'+n for n in theorems];checks.update(names)
 for n in re.findall(r'^#print axioms (\S+)',s,re.M):checks.add(n if n.startswith(('R1Z.','R0')) else ns[0]+'.'+n)
 rows.append(dict(module='R1Z.'+name,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),theorems=names))
# Include the pre-existing full audit's explicit check set as well.
old=lean/'PV_Src_FinalAudit.lean'
checks.update(re.findall(r'^#print axioms (\S+)',old.read_text(),re.M))
imports=''.join('import R1Z.'+name+'\n' for name in sorted(sources))
imports += 'import R1Z.PV_Src_CacheInventory\nimport R1Z.PV_Src_FinalAudit\n'
shards=[]
for i,c in enumerate('ABC'):
 name='PV_Src_FinalAudit6'+c;subset=sorted(checks)[i::3];header=imports+('import R1Z.PV_Src_FinalAudit6A\nimport R1Z.PV_Src_FinalAudit6B\n' if c=='C' else '');text=header+'\n/-! One of three disjoint axiom-report shards; together they audit every PV_Src top theorem. This is not a source/object provenance attestation. -/\n\n'+''.join('#print axioms '+n+'\n' for n in subset)
 if c=='C':
  text += '''\nopen Lean Elab Command
run_cmd do
  let env ← getEnv
  for (mod, data) in env.header.modules.zip env.header.moduleData do
    logInfo m!"PV_IMPORT {mod.module} {mod.hasData}"
    for dep in data.imports do
      logInfo m!"PV_EDGE {mod.module} {dep.module}"
'''
 (lean/(name+'.lean')).write_text(text);shards.append(dict(module='R1Z.'+name,checks=subset,sha256=hashlib.sha256(text.encode()).hexdigest()))
# Exact imported object names from the kernel environment, beyond source scans.
cache_text=imports+'''\nopen Lean Elab Command
run_cmd do
  let env ← getEnv
  for (mod, data) in env.header.modules.zip env.header.moduleData do
    logInfo m!"PV_IMPORT {mod.module} {mod.hasData}"
    for dep in data.imports do
      logInfo m!"PV_EDGE {mod.module} {dep.module}"
'''
if not (lean/'PV_Src_CacheInventory.lean').exists():
 (lean/'PV_Src_CacheInventory.lean').write_text(cache_text)
(e/'resume6-full-audit-plan.json').write_text(json.dumps(dict(modules=rows,total_checks=len(checks),shards=shards),indent=2)+'\n')
print(len(rows),'PV modules;',len(checks),'unique axiom reports across three shards')
