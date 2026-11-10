"""NPC_ B2 local config and preflight (NDZ_prepare_local.py adapted). Read-only RPC; never opens secret bytes."""
import base64,hashlib,json,pathlib,subprocess,sys
L=pathlib.Path('/home/dombarker/project-offloads/codex-cx-devnet2-20261109/local');sys.path.insert(0,str(L))
from r1_devnet_rpc import rpc
NDZ=pathlib.Path('/home/dombarker/project-offloads/codex-cx-devnet-rehearse-20261029')
CLI=NDZ/'NDZ_runtime/extracted/solana-release/bin';URL='http://127.0.0.1:18997'
def public(name):return subprocess.check_output([str(CLI/'solana-keygen'),'pubkey',str(L/'keys'/name)],text=True).strip()
programs={'verifier':'CSnhzGdHQuzMW512CSunJzHrutcmh8ZAFzqx2z1zKorQ','pool':'BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs','registry':'9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q'}
carrier='3jEFrv5Npn3RmFMW1Cbzq5yEiLdeFB5vbBGmnfoqK9vN'
pins={'devnet_verifier':('aspis_r1_cost_probe_program.so','63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299',programs['verifier'],None),
 'pool':('pool.so','e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc',programs['pool'],'Xjb7roDVPDSPoZpUmDVUW5SMx21x7oQEg16dhb5TDXD'),
 'registry':('registry.so','7ad46f0d4b102a7c9699149d23bf6e065b6151feeaca95977d0a3146167d01ab',programs['registry'],None),
 'carrier':('carrier.so','9d45bbcb0d68246993bd080f17f6ae116be48537e1a2c2bfd14602c590740ac2',carrier,'Xjb7roDVPDSPoZpUmDVUW5SMx21x7oQEg16dhb5TDXD')}
artifacts={}
for role,(name,h,_,_) in pins.items():
 p=L/name;actual=hashlib.sha256(p.read_bytes()).hexdigest();assert actual==h,(role,actual)
 artifacts[role]={'path':str(p),'sha256':h}
c={'rpc_url':URL,'genesis_hash':rpc(URL,'getGenesisHash',[]),'payer':public('payer.json'),'programs':programs,'carrier':carrier,'release_artifacts':artifacts,'cli_dir':str(CLI),'signer':str(NDZ/'NDZ_native-target/release/devnet_spend'),'key_dir':str(L/'keys'),'proof_key_dir':str(L/'keys'),'key_namespace':'NPC','proof_cache_reuse':False,'pool_initialize_after_registry':True,'write_delay_seconds':.2,'upload_workers':1}
(L/'out/NPC_local.json').write_text(json.dumps(c,indent=2)+'\n')
A="123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
def b58e(b):
 n=int.from_bytes(b,'big');s=''
 while n:n,r=divmod(n,58);s=A[r]+s
 return '1'*(len(b)-len(b.lstrip(b'\0')))+s
read={'version':rpc(URL,'getVersion',[]),'balance':rpc(URL,'getBalance',[c['payer'],{'commitment':'finalized'}]),'genesis_hash':c['genesis_hash'],'txv1':rpc(URL,'getAccountInfo',['txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL',{'encoding':'base64','commitment':'finalized'}]),'programs':{}}
for role,(name,h,pub,authority) in pins.items():
 prog=rpc(URL,'getAccountInfo',[pub,{'encoding':'base64','commitment':'finalized'}])['value']
 raw=base64.b64decode(prog['data'][0]);assert prog['owner']=='BPFLoaderUpgradeab1e11111111111111111111111' and prog['executable'] and raw[:4]==b'\x02\0\0\0'
 pd=b58e(raw[4:36]);account=rpc(URL,'getAccountInfo',[pd,{'encoding':'base64','commitment':'finalized'}])
 d=base64.b64decode(account['value']['data'][0]);assert d[:4]==b'\x03\0\0\0'
 auth=b58e(d[13:45]) if d[12]==1 else None;assert auth==authority,(role,auth)
 payload=d[45:];elf=(L/name).read_bytes();assert payload[:len(elf)]==elf and not any(payload[len(elf):]),role
 read['programs'][role]={'program':pub,'programdata':pd,'upgrade_authority':auth,'payload_bytes':len(payload),'elf_bytes':len(elf),'elf_sha256':h,'payload_sha256':hashlib.sha256(payload).hexdigest(),'programdata_lamports':account['value']['lamports'],'programdata_slot':int.from_bytes(d[4:12],'little')}
(L/'out/NPC_local-preflight.json').write_text(json.dumps(read,indent=2)+'\n')
assert read['balance']['value']==18353204080
assert base64.b64decode(read['txv1']['value']['data'][0])==bytes.fromhex('010000000000000000')
print(json.dumps({k:{kk:v[kk] for kk in ['upgrade_authority','payload_bytes','elf_sha256']} for k,v in read['programs'].items()},indent=1));print(read['version'])
