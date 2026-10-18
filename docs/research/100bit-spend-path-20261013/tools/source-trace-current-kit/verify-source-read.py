#!/usr/bin/env python3
from pathlib import Path
import tarfile,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/source-read-actual-first-20261018';m=json.loads((E/'packet-manifest.json').read_text());p=E/m['archive'];sha=lambda b:hashlib.sha256(b).hexdigest();digest=lambda v:sha(json.dumps(v,sort_keys=True).encode());assert hashlib.file_digest(p.open('rb'),'sha256').hexdigest()==m['archive_sha256']
with tarfile.open(p) as t:
 sums=json.load(t.extractfile('SHA256SUMS.json'));assert set(t.getnames())==set(sums)|{'SHA256SUMS.json'}
 for n,h in sums.items():assert hashlib.file_digest(t.extractfile(n),'sha256').hexdigest()==h,n
 load=lambda n:json.load(t.extractfile(n));get=lambda n:t.extractfile(n).read();rs=[load(n) for n in sums if n.startswith('successful-targets/')];manifest=load('sources/SOURCE-MANIFEST.json');assert len(rs)==3 and sum(len(r['axioms']['reports']) for r in rs)==15
 predecessor=load('accepted-project-predecessors.json');assert predecessor['prior_archive_sha256']=='7dbd428c81ee45c8aa631e75b075cbed7cac472c6fc559709cae65a556e3de65';allrs={**predecessor['receipts'],**{r['target']:r for r in rs}};d=load('current-object-pins.json');assert len(d['modules'])==6124
 for r in rs:
  assert r['exit_status']==0 and r['axioms']['passed'] and r['process_swaps']==0
  assert all(set(a['axioms'])<={'propext','Classical.choice','Quot.sound'} for a in r['axioms']['reports'])
  assert r['key']['source_sha256']==sha(get('sources/'+manifest['modules'][r['target']]['stage_as']))
  assert r['key']['source_sha256']==sha((R/'lean/bridge-source-trace-current-20261018'/manifest['modules'][r['target']]['stage_as']).read_bytes())
  for suffix,o in r['objects'].items():assert sums['objects/'+r['target']+suffix]==o['sha256']
  for n,pin in r['key']['imports'].items():
   if 'receipt_key' in pin:assert pin['receipt_key']==digest(allrs[n]['key'])
  v=d['modules'][r['target']];assert v['objects']==r['objects'] and v['source_sha256']==r['key']['source_sha256']
 body=get('sources/ExtractedSourceReadFromFirst.lean').decode();assert 'ActualFull25.first_full25' in body and 'decoder_helper_parsePublic' in body and 'parsed_init_fits' in body and 'source_completed_qs' in body
 assert 'typed/ha are separate' in m['scope']
print('PASS3 targets/15standard reports; actual first exact same-q hread, current6124-module output snapshot; typed/ha and custody scope explicit; no compiler invoked')
