import pathlib,json,hashlib,collections,subprocess,ast
E=pathlib.Path(__file__).resolve().parent;s=json.loads((E/'scan.json').read_text());checks=[]
def check(label,value):
 assert value,label;checks.append(label)
check('PASS observations unique',len({(x['pass_output'],x['harness']) for x in s['passes']})==s['pass_count'])
check('all PASS observations have receipt locations and git blobs',all(x['receipt'] and len(x['receipt_blob'])==40 for x in s['passes']))
check('suspension set',set(s['suspended_rows'])=={'V178','V179','V182','V195','V233'})
check('all 407 recount rows retained',len(s['row_consequences'])==407 and len({x['row'] for x in s['row_consequences']})==407)
check('suspensions concern previously closed candidate scopes',all(x['before']=='CLOSED-ON-CANDIDATE' for x in s['row_consequences'] if x['consequence']=='SUSPENDED'))
check('unresolved never exempted',all(s['passes'][i]['copy_builtin_reached'] is None and s['passes'][i]['exemption'] is None for i in s['unresolved']))
check('exposed links depend on reached copies',all(s['passes'][i]['copy_builtin_reached'] is True and s['passes'][i]['property_depends_on_copy'] is True for i in s['exposed']))
check('only named exemptions',all(x['exemption'] in [None,'call-name overapproximation','rejects before the copy on the admitted domain'] for x in s['passes']))
check('no new successful PASS in moving-head delta',not any(x['successful'] for x in json.loads((E/'head-delta-review.json').read_text())))
for p in E.glob('*.py'):ast.parse(p.read_text())
checks.append('authored Python syntax')
graph_count=0
for p in (E/'diagnostics').glob('*/goto-scan.json'):
 for h in json.loads(p.read_text()):
  g=p.parent/h['graph_file'];text=g.read_text();assert hashlib.sha256(text.encode()).hexdigest()==h['graph_sha256'],g
  edges={tuple(l.split(' -> ',1)) for l in text.splitlines() if ' -> ' in l}
  for path in h['copy_paths'].values():
   assert path[0]==h['metadata']['mangled_name'];assert path[-1] in ['memcpy','memmove']
   assert all((a,b) in edges for a,b in zip(path,path[1:])),g
  assert not h['metadata']['attributes']['stubs'];assert not h['metadata']['attributes']['verified_stubs']
  graph_count+=1
checks.append(f'{graph_count} raw goto graph hashes, symbol paths and empty stub lists')
for n in range(1,11):
 p=E/'diagnostics'/f'K{n:02}';r=json.loads((p/'receipt.json').read_text());assert r['exit']==(2 if n==1 else 0)
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert 'Swaps: 0' in (p/'time.log').read_text();assert '--only-codegen' in r['target']
checks.append('10 charged invocations: CLI rejection + 9 capped optimized codegen successes, no solver PASS')
# Verify referenced git evidence is still accessible through its exact blob, independent of moving refs.
objects=sorted({x[k] for x in s['passes'] for k in ['receipt_blob','pass_output_blob']})
p=subprocess.Popen(['git','cat-file','--batch-check'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True)
out,_=p.communicate('\n'.join(objects)+'\n');assert all(' blob ' in l for l in out.splitlines()) and len(out.splitlines())==len(objects)
checks.append(f'{len(objects)} exact historical evidence git blobs accessible')
(E/'validation.json').write_text(json.dumps(dict(status='PASS',checks=checks,pass_observations=s['pass_count'],unresolved=len(s['unresolved']),suspended_rows=s['suspended_rows'],limits='Validation checks index/graph integrity and scope, not universal Kani fidelity or native/deployed correspondence.'),indent=2)+'\n')
print('PASS',len(checks),'checks',graph_count,'graphs',len(s['unresolved']),'unresolved')
