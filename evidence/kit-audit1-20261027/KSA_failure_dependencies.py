from pathlib import Path
import json,collections
E=Path(__file__).resolve().parent
d=json.loads((E/'KSA_dependencies.json').read_text());g={}
for l in (E/'KSA_L023'/'stdout.log').read_text().splitlines():
 if l.startswith('KSA_DEP '):
  r=json.loads(l[8:]);g[r['name']]=r
seeds=['aspis_core.field.QM31.from_le_bytes','XRn_Join_mpow','XRn_Join_qpow','aspis_core.field.M31.inv','aspis_core.circle.secure_ood_circle_point_from_parameter','sampler.circle_sample.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePointErrorSecureCirclePoint.call_once','aspis_core.state_only_hiding.state_only_selected_mask_value','aspis_core.field.wide_exact.WideExact.mul_qm31']
rev=collections.defaultdict(list)
for n,r in g.items():
 for ref in r['refs']:rev[ref].append(n)
paths={s:[s] for s in seeds};q=collections.deque(seeds)
while q:
 n=q.popleft()
 for p in rev[n]:
  if p not in paths:paths[p]=[p]+paths[n];q.append(p)
rows=[]
for t in d['source_theorems']:
 if t['name'] in paths and t['module']==g[t['name']]['module']:rows.append(dict(**t,path=paths[t['name']]))
d['unfaithful_exact_affected']=rows
(E/'KSA_dependencies.json').write_text(json.dumps(d,indent=2)+'\n')
lines=['# Theorems that use a refuted stand-in','',f'{len(rows)} explicit merged source theorems in the queried XR environment have a statement/proof path to one of the eight UNFAITHFUL definitions. Paths include statements, so a rejected-branch theorem may mention a whole function without executing its bad branch. Diagnostic refutations are listed too, and remain valid counterexample theorems.','', '| Theorem | Source | Refuted definition |','|---|---|---|']
for r in rows:lines.append(f"| `{r['name']}` | {r['file']}:{r['line']} | `{r['path'][-1]}` |")
(E/'KSA_UNFAITHFUL_THEOREMS.md').write_text('\n'.join(lines)+'\n');print('exact unfaithful theorem dependencies',len(rows))
