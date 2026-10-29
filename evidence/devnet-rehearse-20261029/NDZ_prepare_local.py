"""Local-only configuration and public preflight. Never opens secret bytes."""
import base64,hashlib,json,pathlib,subprocess,sys
sys.path[:0]=[str(pathlib.Path(__file__).resolve().parents[2]/'scripts'),str(pathlib.Path(__file__).resolve().parents[2])]
from r1_devnet_rpc import rpc
ROOT=pathlib.Path('/home/dombarker/project-offloads/codex-cx-devnet-rehearse-20261029')
E=ROOT/'evidence/devnet-rehearse-20261029';CLI=ROOT/'NDZ_runtime/extracted/solana-release/bin';URL='http://127.0.0.1:18995'
def public(name):return subprocess.check_output([str(CLI/'solana-keygen'),'pubkey',str(E/'keys'/name)],text=True).strip()
programs={'verifier':public('verifier.json'),'pool':'BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs','registry':'9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q'}
artifacts={}
for role,name in [('devnet_verifier','aspis_r1_cost_probe_program.so'),('registry','registry.so'),('pool','pool.so'),('carrier','carrier.so')]:
 p=E/name;artifacts[role]={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
c={'rpc_url':URL,'genesis_hash':rpc(URL,'getGenesisHash',[]),'payer':public('payer.json'),'programs':programs,'carrier':'3jEFrv5Npn3RmFMW1Cbzq5yEiLdeFB5vbBGmnfoqK9vN','release_artifacts':artifacts,'cli_dir':str(CLI),'signer':str(ROOT/'NDZ_native-target/release/devnet_spend'),'key_dir':str(E/'keys'),'proof_key_dir':str(E/'keys'),'key_namespace':'NDZ','proof_cache_reuse':True,'pool_initialize_after_registry':True,'write_delay_seconds':.2}
(E/'NDZ_local.json').write_text(json.dumps(c,indent=2)+'\n')
read={'version':rpc(URL,'getVersion',[]),'balance':rpc(URL,'getBalance',[c['payer'],{'commitment':'finalized'}]),'genesis_hash':c['genesis_hash'],'txv1':rpc(URL,'getAccountInfo',['txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL',{'encoding':'base64','commitment':'finalized'}]),'programs':{}}
for role,pub in list(programs.items())[1:]+[('carrier',c['carrier'])]:
 show=json.loads(subprocess.check_output([str(CLI/'solana'),'--url',URL,'--output','json','program','show',pub]))
 account=rpc(URL,'getAccountInfo',[show['programdataAddress'],{'encoding':'base64','commitment':'finalized'}]);payload=base64.b64decode(account['value']['data'][0])[45:]
 # Clones may include zero allocation suffix. Repository pins use exact ELF extent.
 elf=(E/(role+'.so')).read_bytes();assert payload[:len(elf)]==elf and not any(payload[len(elf):])
 read['programs'][role]={'show':show,'account':account,'elf_sha256':hashlib.sha256(elf).hexdigest()}
(E/'NDZ_local-preflight.json').write_text(json.dumps(read,indent=2)+'\n')
assert read['balance']['value']==18353204080
assert base64.b64decode(read['txv1']['value']['data'][0])==bytes.fromhex('010000000000000000')
