#!/usr/bin/env python3
"""Small allowlisted public RPC read capture. Never loads wallet/key files."""
import base64, datetime, hashlib, json, pathlib, struct, subprocess, urllib.request, time
ROOT=pathlib.Path(__file__).resolve().parent
if (ROOT/'NDQ_RPC_RECEIPTS.json').exists():
 raise SystemExit('Refusing to overwrite frozen receipts; use a new evidence directory for a new authorized check')
URL='https://api.devnet.solana.com'
LOADER='BPFLoaderUpgradeab1e11111111111111111111111'
ALPH='123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
def b58(b):
 n=int.from_bytes(b,'big');s=''
 while n: n,r=divmod(n,58);s=ALPH[r]+s
 return '1'*(len(b)-len(b.lstrip(b'\0')))+s
def sha(b): return hashlib.sha256(b).hexdigest()
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
config=json.loads(subprocess.check_output(['git','show','HEAD:config/r1-devnet.template.json']))
receipt={'schema':'aspis.ndq.rpc-read.v1','endpoint':URL,'cluster':'devnet','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'started_utc':now(),'requests':[],'programs':{},'features':{}}
def save(): (ROOT/'NDQ_RPC_RECEIPTS.json').write_text(json.dumps(receipt,indent=2)+'\n')
def rpc(method,params):
 assert method in {'getAccountInfo','getVersion','getSlot','getEpochInfo','getClusterNodes'}
 i=len(receipt['requests'])+1
 req=json.dumps({'jsonrpc':'2.0','id':i,'method':method,'params':params},separators=(',',':')).encode()
 row={'id':i,'method':method,'params':params,'started_utc':now(),'request_sha256':sha(req),'request_bytes':len(req)}
 (ROOT/f'NDQ_RPC_{i:02d}_request.json').write_bytes(req)
 receipt['requests'].append(row);save()
 try:
  with urllib.request.urlopen(urllib.request.Request(URL,data=req,headers={'Content-Type':'application/json'}),timeout=40) as r:
   raw=r.read();row['http_status']=r.status
  row.update(response_sha256=sha(raw),response_bytes=len(raw),finished_utc=now(),response_file=f'NDQ_RPC_{i:02d}_response.json')
  (ROOT/row['response_file']).write_bytes(raw);save()
  obj=json.loads(raw)
  if 'error' in obj: row['rpc_error']=obj['error'];save();return None
  return obj['result']
 except Exception as e:
  row.update(transport_error=str(e),finished_utc=now());save();return None
 finally: time.sleep(0.8)
def account(key): return rpc('getAccountInfo',[key,{'encoding':'base64','commitment':'finalized'}])
receipt['version']=rpc('getVersion',[])
receipt['slot']=rpc('getSlot',[{'commitment':'finalized'}]);save()
for role,key in dict(config['programs'],carrier=config['carrier']).items():
 out={'program_id':key};receipt['programs'][role]=out
 p=account(key)
 if p is None: out['error']='RPC unavailable';save();continue
 out['program_context']=p['context']
 if p['value'] is None: out['error']='program account absent';save();continue
 v=p['value'];b=base64.b64decode(v['data'][0]);out.update(program_owner=v['owner'],executable=v['executable'],program_account_sha256=sha(b))
 if v['owner']!=LOADER or struct.unpack_from('<I',b)[0]!=2 or len(b)!=36: out['error']='not expected upgradeable Program state';save();continue
 pd=b58(b[4:36]);out['programdata_address']=pd
 d=account(pd)
 if d is None or d['value'] is None:out['error']='ProgramData unavailable';save();continue
 v=d['value'];b=base64.b64decode(v['data'][0]);out.update(programdata_context=d['context'],programdata_owner=v['owner'],programdata_account_sha256=sha(b),programdata_account_bytes=len(b))
 assert v['owner']==LOADER and struct.unpack_from('<I',b)[0]==3
 out['deployment_slot']=struct.unpack_from('<Q',b,4)[0]
 assert b[12] in (0,1)
 out['upgrade_authority']=b58(b[13:45]) if b[12] else None
 elf=b[45:];out.update(loader_header_bytes=45,payload_bytes=len(elf),payload_sha256=sha(elf))
 assert elf[:6]==b'\x7fELF\x02\x01'
 # ELF64 little-endian: keep the entire ELF-declared file extent, including
 # zero bytes belonging to section headers/sections; remove only allocation tail.
 phoff,shoff=struct.unpack_from('<QQ',elf,32);ehsize,phentsize,phnum,shentsize,shnum=struct.unpack_from('<HHHHH',elf,52)
 assert shnum and shnum!=65535
 ends=[ehsize,phoff+phentsize*phnum,shoff+shentsize*shnum]
 for j in range(phnum):
  off=phoff+j*phentsize; po=struct.unpack_from('<Q',elf,off+8)[0];sz=struct.unpack_from('<Q',elf,off+32)[0];ends.append(po+sz)
 for j in range(shnum):
  off=shoff+j*shentsize;typ=struct.unpack_from('<I',elf,off+4)[0];so,sz=struct.unpack_from('<QQ',elf,off+24)
  if typ!=8: ends.append(so+sz) # SHT_NOBITS has no file bytes
 end=max(ends);assert end<=len(elf) and not any(elf[end:])
 out.update(elf_bytes=end,elf_sha256=sha(elf[:end]),trailing_allocation_zero_bytes=len(elf)-end,naive_rstrip_bytes=len(elf.rstrip(b'\0')),naive_rstrip_sha256=sha(elf.rstrip(b'\0')),e_flags=struct.unpack_from('<I',elf,48)[0])
 expected=config['release_artifacts']['devnet_verifier' if role=='verifier' else role]['sha256'];out['historical_config_sha256']=expected;out['matches_historical_config']=expected==out['elf_sha256']
 pins={'verifier':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}
 if role in pins:out.update(release_sha256=pins[role],matches_release=pins[role]==out['elf_sha256'])
 save()
# Exact feature IDs from the locally installed Agave 4.2.1 feature-set source.
sources=list(pathlib.Path('/Users/dominic/.cargo/registry/src').glob('*/agave-feature-set-4.2.1/src/lib.rs'))
assert len(sources)==1
s=sources[0].read_text();receipt['feature_id_source']={'path':str(sources[0]),'sha256':sha(s.encode())}
import re
names=['virtual_address_space_adjustments','disable_sbpf_v0_execution','reenable_sbpf_v0_execution','enable_sbpf_v1_deployment_and_execution','enable_sbpf_v2_deployment_and_execution','enable_sbpf_v3_deployment_and_execution','disable_sbpf_v0_v1_v2_deployment']
for name in names:
 m=re.search(r'pub mod '+name+r'\s*\{\s*solana_pubkey::declare_id!\("([^"]+)"\)',s);assert m,name
 key=m[1];out={'feature_id':key};receipt['features'][name]=out
 d=account(key)
 if d is None:out['status']='unknown'
 elif d['value'] is None:out.update(context=d['context'],status='absent/inactive')
 else:
  v=d['value'];b=base64.b64decode(v['data'][0]);out.update(context=d['context'],owner=v['owner'],data_hex=b.hex())
  assert v['owner']=='Feature111111111111111111111111111111111111' and b[0] in (0,1)
  out['activation_slot']=struct.unpack_from('<Q',b,1)[0] if b[0] else None
  out['status']='active' if b[0] and out['activation_slot']<=d['context']['slot'] else 'pending/inactive'
 save()
receipt['finished_utc']=now();save()
print(json.dumps({k:receipt[k] for k in ['version','slot','programs','features']},indent=2))
