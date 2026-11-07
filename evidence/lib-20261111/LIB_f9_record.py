"""Validate only the F9 continuation receipts; retain previous run evidence."""
from pathlib import Path
import json,re,hashlib,subprocess
E=Path(__file__).resolve().parent
rows=[];allowed={'propext','Classical.choice','Quot.sound'}
for p in sorted(E.glob('LIB_L[0-9][0-9][0-9]/receipt.json')):
 if int(p.parent.name[-3:])<204:continue
 x=json.loads(p.read_text());a=x['attempt'];ad=json.loads((E/(a+'-admission.json')).read_text())
 assert ad['exit']==0 and ad['reservation']['allowed'] is True
 disk=json.loads((E/(a+'-disk-0.json')).read_text());assert disk['free']>=40_000_000_000
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},x['limits']
 assert str(x['swaps'])=='0'
 if x['exit_status']==0:
  for line in x['print_axioms']:
   if 'depends on axioms:' in line:
    names={s.strip() for s in line.split('[',1)[1].split(']',1)[0].split(',') if s.strip()};assert names<=allowed,line
 rows.append({k:x[k] for k in ['attempt','kind','module','source_revision','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']})
assert len(rows)<=80
assert {r['attempt'] for r in rows if r['exit_status']!=0}=={'LIB_L204','LIB_L213','LIB_L215'}
plan=json.loads((E/'LIB_F9_AUDIT_PLAN.json').read_text());audit=[]
for g in plan['groups']:
 p=E/f'LIB_audit/proof{g}/proof{g}.json';x=json.loads(p.read_text());assert x['validated'] and x['exit_status']==0
 for r in x['results']:
  assert r['equal'] and set(r['walked_axioms'])<=allowed and set(r['walked_axioms'])==set(r['collect_axioms'])
  audit.append(r)
assert sorted(r['root'] for r in audit)==sorted(plan['roots'])
changes=subprocess.check_output(['git','diff','--name-only','1e8081cd547^','HEAD'],text=True).splitlines()
assert all(p.startswith('evidence/lib-20261111/') for p in changes)
assert not any(p.stat().st_size>20_000_000 for p in E.rglob('*') if p.is_file())
result=dict(target_established=False,scope_budget=80,scopes_used=len(rows),kani_runs=0,extractions=0,wall_seconds=sum(r['wall_seconds'] for r in rows),max_peak_rss_kib=max(int(r['peak_rss_kib']) for r in rows),swaps=0,attempts=rows,audited_roots=len(audit),audit=audit,successful='L206 total law; L207/L208 install; L209/L210 P/C; L211 TAS TX1; L212 R4; L214 wrong-length Ref; L217 final L/D/V0/VL/P/C bundle; L218/L219 coherent imports; L220-L224 own-root raw ax2; L225 retained closure/export',failures={'LIB_L204':'Scalar coercion simplification repaired from existing Op3I_ParseLaws pattern in L205','LIB_L213':'Rewrite at library projection repaired by typed head law in L214','LIB_L215':'Read-only type inspection missing open RSL; corrected L216'},source_change_scope='Only LIB_ files and own evidence; no shipped/spec/trust change',native_fact_needed=False,remaining='NNG actual094 whole emitted observation/Ref composition, reached child domain proofs; integration actual I.f064/EnvRep; ledger review',unchanged_full_regressions=0)
(E/'LIB_F9_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
(E/'LIB_F9_TRANSCRIPT.tsv').write_text('attempt\tkind\tmodule\texit\twall_seconds\tpeak_rss_kib\tswaps\trevision\n'+''.join('\t'.join(str(r[k]) for k in ['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision'])+'\n' for r in rows))
print(json.dumps({k:result[k] for k in ['scopes_used','wall_seconds','max_peak_rss_kib','swaps','audited_roots']}))
