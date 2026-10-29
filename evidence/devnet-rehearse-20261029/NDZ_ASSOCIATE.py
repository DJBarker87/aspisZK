"""Read-only fresh Pool -> registry -> release verifier association snapshot."""
import base64,hashlib,json,pathlib,subprocess,sys
sys.path[:0]=[str(pathlib.Path(__file__).resolve().parents[2]/'scripts'),str(pathlib.Path(__file__).resolve().parents[2])]
from r1_devnet_rpc import rpc
from r1_devnet_release_gate import base58
C=json.load(open(sys.argv[1]));S=json.load(open(sys.argv[2]));M=json.load(open(pathlib.Path(sys.argv[2]).parent/'mint-setup.json'))
url=C['rpc_url'];pool=C['programs']['pool'];registry=C['programs']['registry'];verifier=C['programs']['verifier'];loader='BPFLoaderUpgradeab1e11111111111111111111111'
cli=pathlib.Path(C['cli_dir'])/'solana'
show=json.loads(subprocess.check_output([str(cli),'--keypair',str(C.get('payer_key',pathlib.Path(C['key_dir'])/'payer.json')),'--url',url,'--output','json','program','show',verifier]));pd=show['programdataAddress'];assert pd==C.get('expected_programdata',pd)
addresses=[S['master'],S['registry_account'],S['entry'],verifier,pd]
a=rpc(url,'getMultipleAccounts',[addresses,{'encoding':'base64','commitment':'finalized'}]);values=a['value'];assert all(values)
raw=[base64.b64decode(v['data'][0]) for v in values];master,reg,entry,program,data=raw
assert values[0]['owner']==pool and len(master)==384 and master[:4]==b'ASM8'
assert master[72:104]==base58(S['master']) and master[104:136]==base58(M['mint'])
policy=master[208:312];assert policy[:4]==b'ASPP' and policy[5]==3 and policy[8:40]==base58(registry) and policy[40:72]==bytes(32) and policy[72:104]==bytes([7])*32
assert values[1]['owner']==registry and len(reg)==256 and reg[:6]==b'ASR2\x03\x02' and reg[8:40]==base58(S['master']) and reg[40:72]==bytes(32) and int.from_bytes(reg[104:112],'little')==3
assert reg[120:152]==base58(registry) and reg[216:248].hex()==C['release_artifacts']['registry']['sha256']
assert values[2]['owner']==registry and len(entry)==320 and entry[:6]==b'ASE2\x03\x01'
assert entry[8:40]==base58(S['master']) and entry[40:72]==base58(verifier)
assert entry[72:104].hex()=='57947313d232641ad8157d66bfaffab11e4c3a99331d18f44bfacab6899737d3'
assert entry[104:136].hex()=='e294afbc14ef6afe76b847def44452f84cc3728064657607b544a539ca9b323a'
assert entry[136:168]==base58(loader) and entry[168:200]==base58(pd) and entry[200:232].hex()==C['release_artifacts']['devnet_verifier']['sha256'] and entry[232:264]==bytes(32) and entry[280:312]==bytes([7])*32
assert int.from_bytes(entry[264:272],'little')<=a['context']['slot']<int.from_bytes(entry[272:280],'little')
assert values[3]['owner']==loader and values[3]['executable'] and len(program)==36 and int.from_bytes(program[:4],'little')==2 and program[4:36]==base58(pd)
assert values[4]['owner']==loader and int.from_bytes(data[:4],'little')==3 and data[12]==0 and len(data[45:])==1563728 and hashlib.sha256(data[45:]).hexdigest()==C['release_artifacts']['devnet_verifier']['sha256']
assert S['master']!='8YRunNHbLqBUzeZYh7VK6jsJDUup4jA1qTcKvPy4i2Lf'
result={'rpc_url':url,'addresses':addresses,'snapshot':a,'fresh_pool':True,'frozen_registry':True,'active_release_entry':True,'immutable_release_programdata':True,'elf_sha256':hashlib.sha256(data[45:]).hexdigest(),'slot':a['context']['slot']}
pathlib.Path(sys.argv[3]).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='snapshot'}))
