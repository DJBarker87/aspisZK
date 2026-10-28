#!/usr/bin/env python3
"""Offline audit of retained RPC bytes; performs no network access."""
import base64, hashlib, json, pathlib, struct, subprocess
root=pathlib.Path(__file__).resolve().parent
r=json.loads((root/'NDQ_RPC_RECEIPTS.json').read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
responses={}
assert len(r['requests'])==17
for row in r['requests']:
 i=row['id'];q=(root/f'NDQ_RPC_{i:02d}_request.json').read_bytes();a=(root/f'NDQ_RPC_{i:02d}_response.json').read_bytes()
 assert sha(q)==row['request_sha256'] and sha(a)==row['response_sha256']
 assert len(q)==row['request_bytes'] and len(a)==row['response_bytes']
 q=json.loads(q);a=json.loads(a)
 assert q['id']==a['id']==i and 'error' not in a
 assert q['method']==row['method'] and q['params']==row['params']
 assert q['method'] in {'getAccountInfo','getVersion','getSlot'}
 if q['method']=='getAccountInfo':
  assert q['params'][1]=={'encoding':'base64','commitment':'finalized'}
  responses[q['params'][0]]=a['result']
 assert row['started_utc']<=row['finished_utc']
for role,p in r['programs'].items():
 program=responses[p['program_id']];data=responses[p['programdata_address']]
 v=program['value'];d=data['value'];b=base64.b64decode(d['data'][0]);prog=base64.b64decode(v['data'][0])
 assert v['executable'] and v['owner']==d['owner']=='BPFLoaderUpgradeab1e11111111111111111111111'
 assert len(prog)==36 and int.from_bytes(prog[:4],'little')==2
 alphabet='123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
 def decode58(s):
  n=0
  for c in s:n=n*58+alphabet.index(c)
  return b'\0'*(len(s)-len(s.lstrip('1')))+n.to_bytes((n.bit_length()+7)//8,'big')
 assert prog[4:]==decode58(p['programdata_address'])
 assert int.from_bytes(b[:4],'little')==3
 assert int.from_bytes(b[4:12],'little')==p['deployment_slot']
 if p['upgrade_authority'] is None: assert b[12]==0
 else: assert b[12]==1 and b[13:45]==decode58(p['upgrade_authority'])
 assert sha(prog)==p['program_account_sha256'] and sha(b)==p['programdata_account_sha256']
 elf=b[45:];assert elf[:6]==b'\x7fELF\x02\x01'
 # Independently validate the section table reaches the payload end in every
 # observed account. Its final 15 zero bytes are therefore ELF file bytes.
 shoff=struct.unpack_from('<Q',elf,40)[0];shentsize,shnum=struct.unpack_from('<HH',elf,58)
 assert shoff+shentsize*shnum==len(elf)==p['elf_bytes']
 assert p['trailing_allocation_zero_bytes']==0
 assert sha(elf)==p['elf_sha256']==p['payload_sha256']==p['historical_config_sha256']
 assert len(elf)-len(elf.rstrip(b'\0'))==15
 assert struct.unpack_from('<I',elf,48)[0]==p['e_flags']==0
 assert p['program_context']==program['context'] and p['programdata_context']==data['context']
for name,f in r['features'].items():
 data=responses[f['feature_id']];assert data['context']==f['context']
 if f['status']=='absent/inactive': assert data['value'] is None
 else:
  v=data['value'];b=base64.b64decode(v['data'][0]);assert v['owner']==f['owner']=='Feature111111111111111111111111111111111111'
  assert b.hex()==f['data_hex'] and b[0]==1 and len(b)==9
  assert int.from_bytes(b[1:],'little')==f['activation_slot']<=data['context']['slot']
for path,h in r['source_pins'].items():
 b=subprocess.check_output(['git','show','efdf060f90fb198006494e91d4a9f23a141a18d3:'+path]);assert sha(b)==h
assert r['programs']['verifier']['matches_release'] is False
assert r['programs']['pool']['matches_release'] is True
print('PASS: 17 raw request/response pairs, four loader links/authorities/ELFs, seven feature observations, 11 frozen source pins; verifier mismatch retained. No network calls.')
