"""Read-only immutable ELF association; never signs or opens wallet files."""
import base64,hashlib,json,pathlib,subprocess,sys
sys.path[:0]=[str(pathlib.Path(__file__).resolve().parents[2]/'scripts'),str(pathlib.Path(__file__).resolve().parents[2])]
from r1_devnet_rpc import rpc
from r1_devnet_release_gate import base58
config=json.load(open(sys.argv[1]));url=config['rpc_url'];role='verifier'
program=config['programs'][role];loader='BPFLoaderUpgradeab1e11111111111111111111111'
cli=pathlib.Path(config['cli_dir'])/'solana'
a=rpc(url,'getAccountInfo',[program,{'encoding':'base64','commitment':'finalized'}]);v=a['value']
assert v and v['owner']==loader and v['executable'];raw=base64.b64decode(v['data'][0]);assert len(raw)==36 and int.from_bytes(raw[:4],'little')==2
show=json.loads(subprocess.check_output([str(cli),'--keypair',str(config.get('payer_key',pathlib.Path(config['key_dir'])/'payer.json')),'--url',url,'--output','json','program','show',program]));pd=show['programdataAddress'];assert pd==config.get('expected_programdata',pd);assert raw[4:36]==base58(pd)
b=rpc(url,'getAccountInfo',[pd,{'encoding':'base64','commitment':'finalized'}]);v=b['value'];assert v and v['owner']==loader and not v['executable'];raw=base64.b64decode(v['data'][0]);assert int.from_bytes(raw[:4],'little')==3 and raw[12]==0
elf=raw[45:];assert len(elf)==1563728 and hashlib.sha256(elf).hexdigest()=='63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299'
result={'program':program,'programdata':pd,'program_account':a,'programdata_account':b,'elf_bytes':len(elf),'elf_sha256':hashlib.sha256(elf).hexdigest(),'immutable':True,'rpc_url':url}
pathlib.Path(sys.argv[2]).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if not k.endswith('_account')}))
