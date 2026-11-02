"""Additional literal-constructor gates; original NEB gates remain unchanged."""
import json,hashlib,re
from NEI_native_pair import check
obj=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def audit(E,R,packet,neb,require):
 require(packet['route']=='D188_LITERAL_CTOR_FULL_CONTEXT' and packet['status']=='CLOSED-CONDITIONAL','ctor method')
 require(packet['suspended_neb_credits_restored']==[] and packet['remaining_inner_hypotheses']==[],'ctor hidden credit/hypothesis')
 for item in packet['lean_evidence']:
  for theorem in item['theorems']:neb.check_receipt(item,theorem)
  d=obj(R/item['receipt'])
  for path,h in d['source_hashes'].items():require(sha(E/path.removeprefix('NEI_generated/'))==h,'ctor current source differs from successful source')
 ex=obj(E/'NEI_E006/NEI_EXTRACTION_PINS.json');require(ex['exit']==0 and ex['charon_exit']==0,'ctor extraction failed')
 require(ex['lock_before']==ex['lock_after'],'ctor extraction lock drift')
 initial=obj(E/'NEI_E001/NEI_EXTRACTION_PINS.json')
 require(all(ex[k]==initial[k] for k in ['charon_sha256','aeneas_sha256','toolchain']),'ctor extraction pins differ')
 for path,h in ex['outputs'].items():
  require(sha(E/path)==h and sha(E/'NEI_DotCtorRaw'/path.split('/')[-1])==h,'edited ctor raw output')
  require(not re.search(r'\b(axiom|sorry|admit|native_decide)\b|FunsExternal|TypesExternal',(E/path).read_text()),'ctor output contains a hole')
 frozen=obj(E/'NEI_FROZEN.json')['crates/aspis-r1-cost-probe/src/fast_pairing.rs'];end=frozen.index('/// Candidate exact accumulator for sums of `WideExact * WideExact`.')
 prefix=(E/'NEI_E006/NEI_isolation_src_NEI_pairing.rs.txt').read_text()
 require(prefix==frozen[:end] and sha(E/'NEI_E006/NEI_isolation_src_NEI_pairing.rs.txt')==ex['pairing_prefix_sha256'],'selected ctor body/record changed')
 base=obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json');rows=[r for r in base['rows'] if r['function']==packet['function']]
 require(rows and packet['frozen_revision']==base['frozen_revision'] and all(r['frozen_body_sha256']==packet['source_body_sha256'] for r in rows),'ctor frozen scope/body')
 pair=check(E,*packet['native_pair'])
 require(sha(R/packet['review']['path'])==packet['review']['sha256'],'ctor association review changed')
 return dict(function=packet['function'],status='CLOSED-CONDITIONAL',route=packet['route'],composed_rows_closed=[],native_pair=pair)
