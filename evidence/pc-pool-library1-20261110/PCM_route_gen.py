from pathlib import Path
import json,hashlib,subprocess,re
E=Path(__file__).resolve().parent
inv=json.loads((E.parent/'pool-inventory2-20261109/NKZ_INVENTORY.json').read_text())
base=json.loads(__import__('lzma').open(E.parent/'pool-ledger1-20261110/PCE_LEDGER.json.xz').read());status={r['id']:r['status']for r in base['rows']}
for folder,pre in [('pc-helpers2-20261110','PCG'),('pc-deposit-children1-20261110','PCF'),('pc-deposit-children2-20261110','PCI'),('pc-terminal-children1-20261110','PCD')]:
 j=json.loads((E.parent/folder/(pre+'_CLOSED.json')).read_text());rs=j if isinstance(j,list)else j['rows']
 for r in rs:status[r.get('id',r.get('row'))]='CLOSED'
nums={int(p.stem.rsplit('_',1)[1])for p in E.glob('PCM_Spec_POOL_*.lean')};rows=[]
guards=dict(json.loads((E/'PCM_GUARD_SITES.json').read_text()))
checks={304:['PCM_E002','PCM_E003','PCM_E008','PCM_E009'],319:['PCM_E006','PCM_E007'],336:['PCM_E004','PCM_E005'],338:['PCM_E004','PCM_E005'],342:['PCM_E004','PCM_E005'],350:['PCM_E010']}
for r in inv['rows']:
 n=int(r['id'].split(':')[1])
 if n not in nums:continue
 lo,hi=r['source_lines'];raw=subprocess.check_output(['git','show','b936275465:'+r['source_file']]);body='\n'.join(raw.decode().splitlines()[lo-1:hi]);own=guards.get(r['id'],[])
 a=[]
 for name in checks.get(n,[]):
  p=E/name/'receipt.json'
  if p.exists():
   rc=json.loads(p.read_text());log=(E/name/'stdout.log').read_text();errors=[l for l in log.splitlines()if 'Error' in l or 'Source:'in l or 'Compiler source:'in l]
   a.append(dict(attempt=name,exit=rc['exit_status'],wall=rc['wall_seconds'],peak_rss_kib=rc['peak_rss_kib'],swaps=rc['swaps'],diagnostic=errors[:5],receipt_sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
 closed=status[r['id']]=='CLOSED'
 if closed:route='CLOSED_CHILD_REUSE_ONLY'
 elif own:route='GUARD_HOLDING_BN_SOURCE_FISSION'
 elif n in [336,338,342]:route='GUARD_FREE_EMITTED_EXTERNAL_ADAPTER_PENDING'
 elif a:route='GUARD_FREE_FRESH_EXTRACTION_FINDING'
 else:route='GUARD_FREE_EXTRACTION_OPEN_BUDGET'
 rows.append(dict(row=r['id'],status=status[r['id']],function=r['function'],frozen_revision='b936275465600469312d1f058cdc91ea2a11f3dc',source_file=r['source_file'],source_lines=r['source_lines'],whole_file_sha256=hashlib.sha256(raw).hexdigest(),body_inventory_sha256=r['frozen_body_sha256'],body_span_sha256=hashlib.sha256(body.encode()).hexdigest(),own_guard_sites=own,route=route,checks=a,gate_closed=False,remaining=('Consume SAME-argument CLOSED child and prove PCM/RSL representation; not re-owned'if closed else 'Fission the actual guard-held segments and preserve borrow-token lifetimes, ordered effects and stop prefixes'if own else 'Instantiate emitted external carriers/functions with standard-axiom CLOSED adapters; emitted templates are text only, never an admitted axiom'if n in [336,338,342]else 'Resolve the exact pinned-tool diagnostic; no failed emission is credited'if a else 'Fresh pinned Charon/Aeneas route check remains; 10 extraction scopes exhausted. Guard-free means no local guard acquisition; transitive guard callees must first consume their own CLOSED/fission packet.')))
report=dict(supporting_only=True,row_credit=0,rule='bm4a/bn route record only; no native proof campaign',pool_files_prechecked='PCM_SOURCE_CHECK.json',new_tools=False,rows=rows,counts={k:sum(x['route']==k for x in rows)for k in sorted({x['route']for x in rows})},findings=['Full-body POOL304 failed at frozen decode_lane_account 500-534, SymbolicToPureValues.ml:878; excluded decoder attempt was also invalid','Full-body POOL319 failed at1392-1409, InterpBorrows.ml:2731','336/338/342 emitted by both pinned tools but external Pubkey/type/to_bytes templates need canonical adapters; template axioms are not admitted','No guard-free row is silently redirected to native replay; unresolved extraction is a finding'])
(E/'PCM_ROUTES.json').write_text(json.dumps(report,indent=1)+'\n');print(json.dumps(report['counts']))
