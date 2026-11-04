"""Validate the exact D561 roots, raw declaration graphs and printed axioms."""
from pathlib import Path
import hashlib,json,re,sys
E=Path(__file__).resolve().parents[2]/'evidence/pv-uc-20261029';ident=sys.argv[1]
P=E/ident;receipt=json.loads((P/'receipt.json').read_text());log=(P/'output.log').read_text()
assert receipt['exit']==0 and receipt['swap']=='0'
STANDARD={'propext','Classical.choice','Quot.sound'};blocks=[];axioms=[];modules={}
for line in log.splitlines():
 for tag in ['NDP_AXIOM ','NDP_MODULE ','NDP_RESULT ']:
  i=line.find(tag)
  if i<0:continue
  x=json.loads(line[i+len(tag):])
  if tag=='NDP_AXIOM ':axioms.append(x)
  elif tag=='NDP_MODULE ':assert x['module'] not in modules;modules[x['module']]=x
  else:blocks.append((x,axioms,modules));axioms=[];modules={}
assert len(blocks)==log.count('NDP_AUDIT_COMPLETE')==8
assert not axioms and not modules
rows=[]
for result,axioms,modules in blocks:
 root=result['root'];stem=root.rsplit('.',1)[1];p=E/'final-gates/d561/axioms'/(stem+'_REACHABLE.txt');raw=p.read_bytes();seen=set(raw.decode().splitlines())
 assert len(seen)==len(raw.decode().splitlines())==result['reachable_constants']
 assert len(modules)==result['loaded_modules']
 closure=set();pending=[result['root_module']]
 while pending:
  m=pending.pop()
  if m in closure:continue
  closure.add(m);pending.extend(modules[m]['imports'])
 assert len(closure)==result['closure_modules']
 assert all(v['in_root_import_closure']==(m in closure) for m,v in modules.items())
 assert len(axioms)==len({v['name'] for v in axioms})==result['all_loaded_axioms']==result['serialized_axioms']
 assert all(v['reachable']==(v['name'] in seen) and v['in_root_import_closure']==(v['module'] in closure) for v in axioms)
 reached={v['name'] for v in axioms if v['reachable']}
 assert reached==set(result['walked_axioms'])==set(result['collect_axioms'])
 printed=next(s for s in receipt['print_axioms_lines'] if s.startswith("'"+root+"'"))
 printed_axioms=set() if 'does not depend' in printed else set(printed.split('depends on axioms: [',1)[1].rstrip(']').split(', '))
 assert printed_axioms==reached
 rows.append(dict(**result,standard_only=reached<=STANDARD,nonstandard_axioms=sorted(reached-STANDARD),reachable_sha256=hashlib.sha256(raw).hexdigest(),print_axioms=printed,explicit_external_parameters=('ExternalTypes (22 carriers), ExternalFuns (104 operations); faithful instance unproved' if root=='PV_UC_ReadyEntry.main' else None)))
all_standard=all(r['standard_only'] for r in rows)
x=dict(status='PASS' if all_standard else 'FAIL: entry reaches unapproved native literal-bound axioms',receipt=ident+'/receipt.json',roots=rows,raw_walk_equals_collect_axioms=True,serialized_kernel_inventory_checked=True,limitations=['Full-entry root is a parametric compilation, not a proof that native external bindings satisfy privacy.','No credit relies on Aeneas builtin fmt/stdout semantics. Native associations remain open; entry main is rejected for its literal-bound axioms.','The fd renderer local source law and generic renderer congruence do not discharge public-transcript/retry/timing laws.','Cached authoritative dependency cohort; no cold/full release closure replay.'])
(E/'final-gates/d561/axioms/validation.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(roots=len(rows),status=x['status'],axioms={r['root']:r['walked_axioms'] for r in rows}),indent=2))

raise SystemExit(0 if all_standard else 1)
