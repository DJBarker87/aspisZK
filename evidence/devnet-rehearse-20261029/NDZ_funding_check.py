"""Read-only writer preflight and conservative funding gate. Generates no signature."""
import base64,hashlib,json,pathlib,subprocess,sys
sys.path[:0]=[str(pathlib.Path(__file__).resolve().parents[2]/'scripts'),str(pathlib.Path(__file__).resolve().parents[2])]
from r1_devnet_rpc import rpc
from r1_devnet_policy import require_key
C=json.load(open(sys.argv[1]));E=pathlib.Path(__file__).parent
assert C['rpc_url']=='https://api.devnet.solana.com'
url=C['rpc_url'];cli=pathlib.Path(C['cli_dir']);keys=pathlib.Path(C['key_dir'])
assert not list(keys.glob(C['key_namespace']+'-*')),'retained fixture namespace already exists: inspect and resume existing receipts, never replace keys'
retained=[require_key(C['payer_key'],cli,C['payer']),require_key(keys/'verifier.json',cli,C['programs']['verifier'])]
assert rpc(url,'getGenesisHash',[])==C['genesis_hash']
buffers=json.loads(subprocess.check_output([str(cli/'solana'),'--keypair',C['payer_key'],'--url',url,'--output','json','program','show','--buffers','--buffer-authority',C['payer']]))
assert buffers=={'buffers':[]},'pre-existing payer buffers: inspect retained keys and recover before a fresh deployment'
elf=pathlib.Path(C['release_artifacts']['devnet_verifier']['path']).read_bytes()
assert len(elf)==1563728 and hashlib.sha256(elf).hexdigest()==C['release_artifacts']['devnet_verifier']['sha256']=='63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299'
assert rpc(url,'getAccountInfo',[C['programs']['verifier'],{'encoding':'base64','commitment':'finalized'}])['value'] is None,'verifier address exists: inspect, do not redeploy'
dependencies={}
for role in ('pool','registry','carrier'):
    address=C['programs'][role] if role!='carrier' else C['carrier']
    show=json.loads(subprocess.check_output([str(cli/'solana'),'--keypair',C['payer_key'],'--url',url,'--output','json','program','show',address]))
    value=rpc(url,'getAccountInfo',[show['programdataAddress'],{'encoding':'base64','commitment':'finalized'}])
    raw=base64.b64decode(value['value']['data'][0]);spec=C['release_artifacts'][role];payload=raw[45:]
    assert value['value']['owner']=='BPFLoaderUpgradeab1e11111111111111111111111' and int.from_bytes(raw[:4],'little')==3
    assert len(payload)>=spec['bytes'] and hashlib.sha256(payload[:spec['bytes']]).hexdigest()==spec['sha256'] and not any(payload[spec['bytes']:])
    if role=='registry':assert raw[12]==0
    dependencies[role]={'show':show,'slot':value['context']['slot'],'elf_sha256':spec['sha256'],'immutable':raw[12]==0}
features={}
for name,address in [('txv1','txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL'),('disable_legacy_sbpf_deployment','B8JJXCy5amZyWG9r7EnUYLwzXSXTxG7GZ1qZ1qggo83g')]:
    account=rpc(url,'getAccountInfo',[address,{'encoding':'base64','commitment':'finalized'}]);value=account['value'];active=False
    if value:
        raw=base64.b64decode(value['data'][0])
        assert value['owner']=='Feature111111111111111111111111111111111111' and len(raw)==9,'unrecognized feature account'
        active=raw[0]==1 and int.from_bytes(raw[1:9],'little')<=account['context']['slot']
    features[name]={'address':address,'active':active,'account':account}
assert features['txv1']['active'],'TxV1 inactive: STOP'
assert not features['disable_legacy_sbpf_deployment']['active'],'frozen legacy-SBPF ELF cannot be newly deployed: STOP and return rebuild decision to owner'
ledger_source=pathlib.Path(sys.argv[3]) if len(sys.argv)>3 else E/'NDZ_RENT_LEDGER.json'
ledger=json.load(open(ledger_source))
rents={n:rpc(url,'getMinimumBalanceForRentExemption',[n,{'commitment':'finalized'}]) for n in sorted({36,1563765,1563773}|{x['data_bytes'] for x in ledger if 'data_bytes' in x})}
fixtures=sum(rents[x['data_bytes']] for x in ledger if 'data_bytes' in x and x['data_bytes'] not in (36,1563773))
locked_fixtures=sum(rents[x['data_bytes']] for x in ledger if 'data_bytes' in x and x['data_bytes'] not in (36,1563773) and x['locked_lamports'])
permanent_verifier=rents[36]+rents[1563773]
# Conservative double-allocation reserve remains above the rehearsed loader
# requirement, which drains the buffer before allocating ProgramData.
fee_reserve=100000000
conservative_peak=rents[1563765]+permanent_verifier+fixtures+fee_reserve
balance=rpc(url,'getBalance',[C['payer'],{'commitment':'finalized'}])
result={'features':features,'ledger_source':str(ledger_source),'retained_keys':retained,'dependencies':dependencies,'rpc_url':url,'balance':balance,'rent_quotes':rents,'verifier_permanently_locked_lamports':permanent_verifier,'fixture_rent_lamports':fixtures,'fixture_locked_budget_lamports':locked_fixtures,'permanent_locked_budget_lamports':permanent_verifier+locked_fixtures,'fee_reserve_lamports':fee_reserve,'conservative_peak_lamports':conservative_peak,'headroom_lamports':balance['value']-conservative_peak,'funding_pass':balance['value']>=conservative_peak,'signatures_generated':0}
pathlib.Path(sys.argv[2]).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ('retained_keys','rent_quotes')},indent=2))
assert result['funding_pass'],'insufficient conservative peak funding: STOP'
