"""Fresh actual-body Wide constructor packet; no inherited native verdicts."""
import json,hashlib,re
from pathlib import Path
from NEI_native_pair import check
obj=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
FUNCTION='crates/aspis-core/src/field/wide_exact.rs::WideExact::from_limbs'
def audit(E,R,p,neb,require):
 require(p['function']==FUNCTION and p['route']=='D188_ACTUAL_WIDE_CTOR' and p['status']=='CLOSED-CONDITIONAL','wide packet scope')
 require(p['domain']=='All eight raw U32 words; rejection and success both included' and p['remaining_inner_hypotheses']==[] and p['suspended_neb_credits_restored']==[],'wide hidden domain/credit')
 for item in p['lean_evidence']:
  for theorem in item['theorems']:neb.check_receipt(item,theorem)
  d=obj(R/item['receipt'])
  for path,h in d['source_hashes'].items():require(sha(E/path.removeprefix('NEI_generated/'))==h,'wide successful source differs')
 ex=obj(E/'NEI_E008/NEI_EXTRACTION_PINS.json');require(ex['exit']==0 and ex['charon_exit']==0 and ex['lock_before']==ex['lock_after'],'wide extraction/lock')
 first=obj(E/'NEI_E001/NEI_EXTRACTION_PINS.json');require(all(ex[k]==first[k] for k in ['charon_sha256','aeneas_sha256','toolchain']),'wide translator pins')
 require('--include' in ex['charon_command'] and 'aspis_core::field' in ex['charon_command'],'opaque field methods')
 for path,h in ex['outputs'].items():
  require(sha(E/path)==h and sha(E/'NEI_WideCtorRaw'/Path(path).name)==h,'changed raw wide output')
  require(not re.search(r'\b(axiom|sorry|admit|native_decide)\b|FunsExternal|TypesExternal',(E/path).read_text()),'wide opaque/admitted emitted definition')
 require((E/'NEI_E008/NEI_isolation_src_lib.rs.txt').read_text()=='use aspis_core::field::WideExact as E;\npub fn NEI_wide_from_limbs(words:[u32;8])->Option<E>{E::from_limbs(words)}\n','changed isolated wrapper')
 base=obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json');rows=[r for r in base['rows'] if r['function']==FUNCTION]
 require(rows and all(r['frozen_body_sha256']==p['source_body_sha256'] for r in rows) and p['frozen_revision']==base['frozen_revision'],'wide source/body scope')
 pair=check(E,*p['native_pair'])
 source=obj(E/'NEI_FROZEN.json')['crates/aspis-core/src/field/wide_exact.rs']
 for attempt in p['native_pair'][:2]:
  frozen=obj(E/(attempt+'-frozen-source-check.json'))
  require('crates/aspis-core/src/field/wide_exact.rs' in frozen['files'] and frozen['passed'],'wide actual method not frozen-checked')
 require(sha(R/p['review']['path'])==p['review']['sha256'],'wide review changed')
 return dict(function=FUNCTION,status=p['status'],route=p['route'],native_pair=pair,composed_rows_closed=[])
def check_some(row,o,ext,rc):
 assert row['function']==FUNCTION and o['call'].get('expression',o['call'].get('syntax'))=='Some' and o['call']['line']==213,'not exact wide Some constructor'
 assert ext['source_body_sha256']==row['frozen_body_sha256'] and ext['syntax']=='Some' and ext['line']==213,'wide constructor source mismatch'
 assert ext['theorems']==['NEI_WideCtorAssociation.same_result'] and any(ext['theorems'][0] in e['theorems'] for e in rc['lean_evidence']),'missing actual Option/record association'
