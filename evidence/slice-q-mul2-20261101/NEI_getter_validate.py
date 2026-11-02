import json,hashlib
from NEI_native_pair import check
obj=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def audit(E,R,p,neb,require):
 require(p['route']=='D188_ACTUAL_GETTER_FRAME' and p['status']=='CLOSED-CONDITIONAL','getter route')
 require(p['remaining_inner_hypotheses']==[] and p['suspended_neb_credits_restored']==[],'getter hidden assumptions/credit')
 for item in p['lean_evidence']:
  for theorem in item['theorems']:neb.check_receipt(item,theorem)
  receipt=obj(R/item['receipt'])
  for n,h in receipt['source_hashes'].items():require(sha(E/n.removeprefix('NEI_generated/'))==h,'getter current proof source')
 pair=check(E,*p['native_pair'])
 base=obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json');rows=[r for r in base['rows'] if r['function']==p['function']]
 require(rows and p['frozen_revision']==base['frozen_revision'] and all(r['frozen_body_sha256']==p['source_body_sha256'] for r in rows),'getter frozen body')
 require(sha(R/p['review']['path'])==p['review']['sha256'],'getter review changed')
 raw=(E.parent/'slice-q-mul-20261029/NEG_RowIsolated/Funs.lean').read_text()
 require('def '+p['function'].rsplit('::',1)[1] in raw,'getter actual definition missing')
 return dict(function=p['function'],status='CLOSED-CONDITIONAL',route=p['route'],native_pair=pair,composed_rows_closed=[])
