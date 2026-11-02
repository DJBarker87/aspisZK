"""Check the three focused raw-walk inventories, module DAGs and printed axioms."""
from pathlib import Path
import hashlib,json,re,sys

E=Path(__file__).resolve().parents[2]/'evidence/pv-uc-20261029'
P=E/'lean75005';log=(P/'output.log').read_text();receipt=json.loads((P/'receipt.json').read_text())
assert receipt['exit']==0 and receipt['swap']=='0'
cg=receipt['elaboration_result']['cgroup']
assert (cg['memory.high'],cg['memory.max'],cg['memory.swap.max'],cg['pids.max'])==('6442450944','8589934592','0','64')
STANDARD={'propext','Classical.choice','Quot.sound'}
blocks=[];axioms=[];modules={}
for line in log.splitlines():
 for tag in ['NDP_AXIOM ','NDP_MODULE ','NDP_RESULT ']:
  i=line.find(tag)
  if i<0:continue
  value=json.loads(line[i+len(tag):])
  if tag=='NDP_AXIOM ':axioms.append(value)
  elif tag=='NDP_MODULE ':
   assert value['module'] not in modules
   modules[value['module']]=value
  else:
   blocks.append((value,axioms,modules));axioms=[];modules={}
assert len(blocks)==log.count('NDP_AUDIT_COMPLETE')==3
assert not axioms and not modules
rows=[]
for result,axioms,modules in blocks:
 root=result['root'];stem=root.rsplit('.',1)[1]
 path=E/'final-gates/axioms'/(stem+'_REACHABLE.txt')
 raw=path.read_bytes();names=raw.decode().splitlines();seen=set(names)
 assert len(seen)==len(names)==result['reachable_constants']
 assert hashlib.sha256(raw).hexdigest()==Path(str(path)+'.sha256').read_text().strip()
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
 assert reached==set(result['walked_axioms'])==set(result['collect_axioms'])==STANDARD
 printed=next(s for s in receipt['print_axioms_lines'] if s.startswith("'"+root+"'"))
 assert set(printed.split('depends on axioms: [',1)[1].rstrip(']').split(', '))==reached
 rows.append(dict(**result,standard_only=True,reachable_sha256=hashlib.sha256(raw).hexdigest(),
    imported_nonstandard_axioms=[v['name'] for v in axioms if v['in_root_import_closure'] and v['name'] not in STANDARD],
    print_axioms=printed))
out=dict(status='PASS for precisely these three compiled roots',roots=rows,
    receipt='lean75005/receipt.json',log_sha256=hashlib.sha256(log.encode()).hexdigest(),
    raw_walk_equals_collect_axioms=True,serialized_kernel_inventory_checked=True,
    not_audited=['PV_UC_Entry full entry: missing faithful external bindings',
                 'PV_UC_Decoder Funs: emitted shift type mismatch'],
    limitations=['Cached authoritative libraries, not a cold release closure replay.',
                 'Imported nonstandard axioms are inventoried and unreachable from these roots.',
                 'Negative formatting diagnostics and a Wallet type do not discharge native or privacy premises.'])
p=E/'final-gates/axioms/validation.json';encoded=json.dumps(out,indent=2)+'\n'
if '--check' in sys.argv:assert p.read_text()==encoded
else:p.write_text(encoded)
print(json.dumps(dict(status=out['status'],roots={r['root']:r['walked_axioms'] for r in rows})))
