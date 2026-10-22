#!/usr/bin/env python3
import hashlib,json,pathlib,sys
p=pathlib.Path(__file__).resolve().parent
m=json.loads((p/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1'
assert m['launch']['source_revision_at_launch']=='UNKNOWN_NOT_CAPTURED'
assert m['modules'][0]['exit_status']==0 and m['modules'][0]['swap_bytes']==0
assert m['modules'][0]['axioms']==['propext','Classical.choice','Quot.sound']
for f in m['files']:
 q=p/f['path']; b=q.read_bytes(); assert len(b)==f['size_bytes'] and hashlib.sha256(b).hexdigest()==f['sha256'],f['path']
 assert q.suffix not in {'.olean','.ilean','.c','.o'}
s=p/'sources/S4Tx2TwelveReturnedLocalBatchesV1.lean'
assert hashlib.sha256(s.read_bytes()).hexdigest()==m['modules'][0]['source_sha256']
assert 'full_tx2_twelve_actual_returned_local_batches' in s.read_text()
for n,i in m['direct_import_source_map'].items():
 q=p/'dependencies'/f'{n}.lean'; assert hashlib.sha256(q.read_bytes()).hexdigest()==i['source_sha256'],n
 assert i['selected_object_sha256']==i['expected_object_sha256'],n
assert not list(p.rglob('*.olean'))
print('PASS',m['packet'],'files',len(m['files']))
