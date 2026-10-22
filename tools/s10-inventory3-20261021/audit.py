#!/usr/bin/env python3
"""Integrity and negative checks. Completeness failure remains a failure."""
import copy,importlib.util,json,resource,subprocess,sys,time
from pathlib import Path
start=time.monotonic();HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('s10pass3',HERE/'reconcile.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
checks=[];manifest=m.load(m.E/'build-manifest.json');pins={r['artifact']:r for r in m.load(m.B/'evidence/s10-inventory-20261021/inventory.json')['declarations'] if r['evidence']=='linked symbol'}
expected={'default':'dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34','devnet':'fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}
assert manifest['source_files_rehashed']==488
assert manifest['frozen_source_revision']=='b2727acd3abf79315d18b754a260f58f4b1c6326'
for b in manifest['builds']:
 d=m.E/b['name'];r=m.load(d/'receipt.json');assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert m.sha((d/'receipt.json').read_bytes())==b['receipt']['sha256']
 assert r['swaps']==0
 if b['comparison']:
  c=b['comparison'];assert r['exit_status']==0 and c['byte_identical'] and c['sha256']==c['expected_sha256']==expected[c['mode']]
 else:assert b['name']=='build-default-v1' and r['exit_status']!=0
 for a in b['artifacts']:
  local=d/Path(a['path']).name
  if local.exists():assert local.stat().st_size==a['bytes'] and m.sha(local.read_bytes())==a['sha256'],local
 for p in d.glob('*.mono.txt'):
  # A failed compiler can emit an empty log; it is never used as evidence of a body.
  if r['exit_status']==0:assert p.stat().st_size
checks.append('three frozen ELF pins reproduced; source rehash and every retained receipt/cap/mono pin checked; failed option preflight preserved')
outputs=m.build()
for name,x in outputs.items():assert (m.E/name).read_bytes()==m.encoded(x),name
checks.append('all reconciliation outputs regenerate byte-for-byte')
original_load=m.load
def rejects(pathname,mutate):
 def bad(p):
  value=original_load(p)
  if p.name==pathname:value=copy.deepcopy(value);mutate(value)
  return value
 m.load=bad
 try:
  try:m.build()
  except (AssertionError,StopIteration):return
  raise AssertionError('mutation accepted: '+pathname)
 finally:m.load=original_load
rejects('frontiers-default.json',lambda x:x[0]['frozen_bodies'].append(x[0]['frozen_bodies'][0]))
rejects('frontiers-default.json',lambda x:x.pop())
rejects('ordering-observations.json',lambda x:[r.update(dominance=[]) for r in x['functions'] if r['mode']=='default' and r['header'].startswith('fn tx1(')])
checks.append('ambiguous body, missing frontier and missing actual CFG order facts are rejected')
for mode,observations in [('default',40),('devnet',40),('pool',29)]:
 rows=m.load(m.E/('frontiers-'+mode+'.json'));assert sum(len(r['frozen_bodies'])==1 for r in rows)==observations
assert len(outputs['open-frontier-specifications.json'])==18
assert all(r['status']=='SPECIFIED_NOT_DISCHARGED' for r in outputs['open-frontier-specifications.json'])
checks.append('all 40 verifier bodies and 18 specifications retained without treating proposed specs as discharged joins')
old=m.B/'evidence/s10-inventory-20261021/OraclePortS10ModelInventory-7/receipt.json';proof=m.load(old)
assert proof['exit_status']==0 and proof['source_sha256']==m.sha((m.B/'lean/OraclePortS10ModelInventory.lean').read_bytes())
assert len(proof['print_axioms'])==4 and all(l.endswith('[propext, Classical.choice, Quot.sound]') for l in proof['print_axioms'])
coverage=m.load(m.E/'coverage-preflight.json');assert coverage['exit_status']==2 and not coverage['lean_compiler_invoked']
assert coverage['core_sha256']==m.sha((m.B/'lean/OraclePortJoinSplitCore.lean').read_bytes())
checks.append('actual Cone/Site preflight obstruction recorded; unchanged model-only source and four standard-axiom audits reused')
gates=[]
for script in ['tools/s10-inventory2-20261021/reconcile.py','tools/s10-inventory3-20261021/reconcile.py']:
 p=subprocess.run([sys.executable,'-B',str(m.R/script),'--check','--require-complete'],cwd=m.R,text=True,capture_output=True)
 assert p.returncode==2,p.stdout+p.stderr
 gates.append(dict(target=script,exit_status=p.returncode,stdout=p.stdout,stderr=p.stderr))
checks.append('original and pass-three completeness gates both exit 2; no success relabeling')
assert all(p.stat().st_size<=5_000_000 for p in m.E.rglob('*.json'))
checks.append('no committed derived JSON exceeds 5 MB')
u=resource.getrusage(resource.RUSAGE_SELF)
r=dict(schema='s10-pass3-integrity-receipt-v1',target='tools/s10-inventory3-20261021/audit.py',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=m.R,text=True).strip(),source_sha256=m.sha(Path(__file__).read_bytes()),exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,swaps=u.ru_nswap,print_axioms=proof['print_axioms'],axioms_scope='Reused unchanged model-only results; no new theorem, final source coverage instance or source ordering join claimed',checks=checks,completeness_gates=gates,input_hashes={str(p.relative_to(m.R)):m.sha(p.read_bytes()) for p in sorted(HERE.glob('*.py'))})
(m.E/'validation.json').write_bytes(m.encoded(r));print(json.dumps(dict(exit_status=0,checks=len(checks),completeness_gates=[g['exit_status'] for g in gates],wall_seconds=r['wall_seconds'])))
