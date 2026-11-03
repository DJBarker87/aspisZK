"""Actual immutable field-body D188 gate; no arithmetic Kani credit."""
from pathlib import Path
import json,hashlib,re,copy
obj=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
E=Path(__file__).resolve().parent;R=E.parent.parent
SCOPE=obj(E/'NEI_FIELD_SCOPE.json');FUNCTIONS=SCOPE['functions'];OPS=SCOPE['ops']
def proof(E,neb,item):
 for n in item['theorems']:neb.check_receipt(item,n)
 d=obj(R/item['receipt'])
 for n,h in d['source_hashes'].items():assert sha(E/n.removeprefix('NEI_generated/'))==h,'changed successful field proof'
def native(E):
 ds=[obj(E/a/'receipt.json') for a in ['NEI_N013','NEI_N014']]
 assert [d['exit_status'] for d in ds]==[0,101] and ds[0]['source_hashes']==ds[1]['source_hashes']
 assert ds[0]['source_hashes']==APPROVED_NATIVE_SOURCES,'unreviewed native field comparison/source'

 env=copy.deepcopy(ds[0]['env']);env['NEI_WRONG']='1';assert env==ds[1]['env']
 for a,d in zip(['NEI_N013','NEI_N014'],ds):
  assert d['limits']==dict(zip(['memory.high','memory.max','memory.swap.max','pids.max'],['6442450944','8589934592','0','64'])) and d['swaps']=='0'
  assert d['env']['CARGO_NET_OFFLINE']=='true' and d['env']['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']=='true'
  for n,h in d['source_hashes'].items():assert sha(E/a/'sources'/n)==h
  pins=obj(E/a/'NEI_NATIVE_PINS.json');assert pins['core_features']==['r0'] and pins['lock_before']==pins['lock_after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  text=(E/a/'stdout.log').read_text();cmd=json.loads(next(l for l in text.splitlines() if l.startswith('{"command"')))['command'];assert '--release' in cmd and '--locked' in cmd and '--offline' in cmd and cmd[cmd.index('--features')+1]=='r0'
  assert ('20 passed; 0 failed' if a=='NEI_N013' else '0 passed; 20 failed') in text
  if a=='NEI_N013':
   assert set(re.findall(r'^test field::wide_exact::NEI_field_fidelity::NEI_field_(\w+) \.\.\. ok$',text,re.M))=={o[0] for o in OPS}
  else:
   assert set(re.findall(r'^    field::wide_exact::NEI_field_fidelity::NEI_field_(\w+)$',text,re.M))=={o[0] for o in OPS},'missing named failure summary'
   assert text.count('assertion `left == right` failed')==20
 assert obj(E/'NEI_N013/NEI_NATIVE_PINS.json')==obj(E/'NEI_N014/NEI_NATIVE_PINS.json')
 return dict(positive='NEI_N013',negative='NEI_N014',tests=20,fixtures=100,universal_native_proof=False,kani_credit=0)
def audit(p,neb):
 assert p['function'] in FUNCTIONS and p['route']=='D188_ACTUAL_IMMUTABLE_FIELD' and p['status']=='CLOSED-CONDITIONAL'
 assert p['domain']=='All typed field carriers; complete Result fidelity. Canonical mathematical laws retain their existing model domains.'
 assert p['new_kani_credits']==[] and p['suspended_neb_credits_restored']==[] and p['remaining_inner_hypotheses']==[]
 for item in p['lean_evidence']:proof(E,neb,item)
 names={n for item in p['lean_evidence'] for n in item['theorems']}
 tag=OPS[FUNCTIONS.index(p['function'])][0];kind=OPS[FUNCTIONS.index(p['function'])][2]
 module={'word':'NEI_FieldScalar','cm':'NEI_FieldCM','qm':'NEI_FieldQM','wide':'NEI_FieldWide'}[kind]
 lemma={'m_reduce':'m_reduce_u64'}.get(tag,tag)
 required={module+'.'+lemma,'NEI_FieldFrames.'+tag,'NEI_FieldFrames.widen'}
 assert set(p['required_theorems'])==required and required<=names,'missing specific complete operator/field frame association'
 ex=obj(E/'NEI_E001/NEI_EXTRACTION_PINS.json');assert ex['exit']==0 and ex['charon_exit']==0 and ex['lock_before']==ex['lock_after']
 assert '--include' in ex['charon_command'] and 'aspis_core::field' in ex['charon_command']
 for n,h in ex['outputs'].items():
  raw=E/n;assert sha(raw)==h and sha(E/'NEI_LineFull'/Path(n).name)==h
  assert not re.search(r'\b(axiom|sorry|admit|native_decide)\b|FunsExternal|TypesExternal',raw.read_text())
 base=obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json');rows=[r for r in base['rows'] if r['function']==p['function']];assert rows and p['frozen_revision']==base['frozen_revision'] and all(r['frozen_body_sha256']==p['source_body_sha256'] for r in rows)
 path=p['function'].split('::')[0];frozen=obj(E/'NEI_FROZEN.json')[path];lo,hi=rows[0]['frozen_body_byte_range'];body=frozen.encode()[lo:hi];assert hashlib.sha256(body).hexdigest()==p['source_body_sha256']
 code=re.sub(rb'/\*.*?\*/|//[^\n]*',b'',body,flags=re.S)
 assert not re.search(rb'&\s*mut\b|\bunsafe\b|\bextern\b|\bwhile\b|\bfor\b|asm!',code),'mutable/foreign/loop field shape'
 for module,h in APPROVED_MODELS.items():assert sha(E/(module+'.lean'))==h,'unreviewed field statement/source'
 assert sha(R/p['review']['path'])==p['review']['sha256']
 return dict(function=p['function'],status=p['status'],route=p['route'],native=native(E),composed_rows_closed=[])

APPROVED_MODELS={'NEI_FieldCarriers': '54e19fd2ad9afe0f766c903e9f65ffcd864908bc47c8564e535ba527032961fe', 'NEI_FieldScalar': 'dd722c7804fcadb17891f82fd5503cf82308dd8ec82de4704535dc9537401ae2', 'NEI_FieldCM': '27fc91ea456cc54bd9bf7aeb6057f58903aa71ae11c9db41baf63cd0cd24b9fd', 'NEI_FieldQM': 'febba183708ae7ce2b1fa51cf6d37e24b517ca7ff4f9a4dad767ae789a1486c9', 'NEI_FieldWide': '8209cf69a729dde7b635dad7a9bba09de75e4ffce4e2397d918a2fc682643446', 'NEI_FieldFrames': '9079ffabcd9c71a50141844a5225edcb1d216a601df282d07293dcf406b45fbf'}

APPROVED_NATIVE_SOURCES={'NEI_field_native.py': 'b48ef69df203829f68e7cbdf076cef7fce83be8748eaee4ae36b2e6b83648346', 'NEI_field_native.rs': '6dc7c70e29f3222a5a74c46dc61d1cac4788e49e68d61898b86d9bed3e74725f', 'NEI_FROZEN.json': 'c9de366045aba5b88908e26fdfedc54c962c75437646b3577953d6d716109c72', 'NEI_FIELD_TEST_INPUTS.json': '8b7a63a7f9412d05ee2365bef9689b79976c0d4fc6594a4497fb05abaa97598f'}
