#!/usr/bin/env python3
"""Public inventory of retained task keys and known controlled accounts; no cleanup."""
import base64,hashlib,json,os,pathlib,stat,subprocess,sys
from r1_devnet_rpc import rpc
C=json.load(open(sys.argv[1]));out=pathlib.Path(sys.argv[2]);assert not out.exists()
cli=pathlib.Path.home()/'.local/share/solana/install/active_release/bin/solana-keygen'
alphabet='123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
def b58(data):
 n=int.from_bytes(data,'big');s=''
 while n:n,r=divmod(n,58);s=alphabet[r]+s
 return '1'*(len(data)-len(data.lstrip(b'\0')))+s
keys=[]
for p in sorted([*pathlib.Path('keys').glob('*.json'),*pathlib.Path('artifacts').glob('**/*-keypair.json')]):
 assert not p.is_symlink();os.chmod(p,0o600)
 address=subprocess.check_output([str(cli),'pubkey',str(p)],text=True).strip();keys.append({'path':str(p),'pubkey':address,'mode':oct(stat.S_IMODE(p.stat().st_mode)),'retained':True})
setup=json.load(open('receipts/spend/setup-plan.json'));extra=[setup['vault'],setup['vault_authority'],setup['master'],setup['registry_account'],setup['entry'],*setup['lanes']]
extra += [json.load(open(f'receipts/spend/{op}-proof-plan.json'))['marker'] for op in ['transfer','withdrawal']]
addresses=sorted({x['pubkey'] for x in keys}|set(extra));r=rpc(C['rpc_url'],'getMultipleAccounts',[addresses,{'commitment':'finalized','encoding':'base64'}]);accounts={}
for address,a in zip(addresses,r['value']):
 if a is None:accounts[address]={'exists':False,'lamports':0};continue
 data=base64.b64decode(a['data'][0]);v={'exists':True,'lamports':a['lamports'],'owner':a['owner'],'executable':a['executable'],'data_bytes':len(data),'data_sha256':hashlib.sha256(data).hexdigest()}
 if a['owner']=='TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA':
  if len(data)==165:v['token']={'mint':b58(data[:32]),'authority':b58(data[32:64]),'amount_base_units':int.from_bytes(data[64:72],'little')}
  if len(data)==82:v['mint']={'authority':b58(data[4:36]) if int.from_bytes(data[:4],'little')==1 else None,'supply_base_units':int.from_bytes(data[36:44],'little'),'decimals':data[44],'freeze_authority':b58(data[50:82]) if int.from_bytes(data[46:50],'little')==1 else None}
 accounts[address]=v
programs={}
for role in ['verifier','pool','registry','carrier']:
 meta=json.load(open(f'receipts/deploy-fresh/{role}-programdata.json'));a=rpc(C['rpc_url'],'getAccountInfo',[meta['address'],{'commitment':'finalized','encoding':'base64'}]);v=a['value'];assert v['owner']=='BPFLoaderUpgradeab1e11111111111111111111111' and not v['executable'];data=base64.b64decode(v['data'][0]);assert int.from_bytes(data[:4],'little')==3
 spec=C['release_artifacts']['devnet_verifier' if role=='verifier' else role];h=hashlib.sha256(data[45:]).hexdigest();assert h==spec['sha256']
 programs[role]={'programdata':meta['address'],'lamports':v['lamports'],'last_deploy_slot':int.from_bytes(data[4:12],'little'),'upgrade_authority':b58(data[13:45]) if data[12] else None,'elf_sha256':h,'readback_context_slot':a['context']['slot']}
 assert programs[role]['upgrade_authority']==(None if role in ['verifier','registry'] else C['payer'])
recovery=[{'path':str(p),'mode':oct(stat.S_IMODE(p.stat().st_mode)),'retained':True} for p in pathlib.Path('receipts/spend').glob('*-proof-private/note-recovery.json')]
assert len(recovery)==2 and all(v['mode']=='0o600' for v in recovery)
result={'scope':'Known task keys, balances and authorities; no cleanup or refund attempted','context_slot':r['context']['slot'],'key_directory_mode':oct(stat.S_IMODE(pathlib.Path('keys').stat().st_mode)),'keys':keys,'accounts':accounts,'programs':programs,'note_recovery_files':recovery,'retained_refund_destination':C['payer'],'refund_signatures':[]}
out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'keys_retained':len(keys),'payer_lamports':accounts[C['payer']]['lamports'],'vault_token':accounts[setup['vault']]['token'],'programdata_pins_verified':True,'recovery_files_retained':len(recovery)},indent=2))
