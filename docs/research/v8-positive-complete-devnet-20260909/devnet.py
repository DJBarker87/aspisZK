#!/usr/bin/env python3
"""Isolated, resumable devnet instructions. Private keys never leave the local key directory.

TxV1 encoding follows solana-message 4.2.4 and solana-transaction 4.1.5.
Every submitted application transaction is first simulated with its exact signed bytes.
"""
import base64, datetime, hashlib, json, os, pathlib, struct, sys, time, urllib.request
import fcntl
from solders.keypair import Keypair
from solders.pubkey import Pubkey

HERE = pathlib.Path(__file__).resolve().parent
PRIVATE = pathlib.Path.home()/'.local/share/aspis/v8-positive-complete-20260909'
CONFIG = json.loads((HERE/'identities.json').read_text())
EVIDENCE = HERE/'evidence'/CONFIG.get('evidence_run','live')
EVIDENCE.mkdir(parents=True, exist_ok=True)
RPC = 'https://api.devnet.solana.com'
RPC_SECRET = ''
if os.environ.get('ASPIS_RPC_PROVIDER') == 'helius':
    # Read only this API credential; construct a fixed devnet host regardless of its original use.
    config = pathlib.Path('/Users/dominic/ZK/private/aspis-config/v5-mainnet-20260724/helius.env')
    values = dict(line.split('=',1) for line in config.read_text().splitlines() if '=' in line and not line.lstrip().startswith('#'))
    RPC_SECRET = values['HELIUS_API_KEY'].strip().strip('\"').strip("'")
    RPC = 'https://devnet.helius-rpc.com/?api-key='+RPC_SECRET
GENESIS = 'EtWTRABZaYq6iMfeYKouRu166VU2xqa1wcaWoxPkrZBG'
IDS = CONFIG['programs_and_accounts']
PLAN = json.loads((HERE/'plan.json').read_text())
SYSTEM = '11111111111111111111111111111111'
TOKEN = 'TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA'
CU = 1_200_000
_RECENT_BLOCKHASH = None
_RECENT_BLOCKHASH_TIME = 0.0
def recent_blockhash(force=False):
    global _RECENT_BLOCKHASH, _RECENT_BLOCKHASH_TIME
    if force or _RECENT_BLOCKHASH is None or time.monotonic()-_RECENT_BLOCKHASH_TIME>20:
        _RECENT_BLOCKHASH=rpc('getLatestBlockhash',[{'commitment':'finalized'}])['value']
        _RECENT_BLOCKHASH_TIME=time.monotonic()
    return _RECENT_BLOCKHASH
def save(path, value):
    path.write_text(json.dumps(value, indent=2)+'\n')
class RpcRateLimited(RuntimeError): pass
def _pace_rpc():
    # One shared clock across upload processes/threads; no credential in the file.
    fd=os.open(PRIVATE/'rpc-rate-lock',os.O_RDWR|os.O_CREAT,0o600)
    with os.fdopen(fd,'r+') as f:
        fcntl.flock(f,fcntl.LOCK_EX)
        previous=float(f.read() or '0')
        delay=0.35-(time.monotonic()-previous)
        if delay>0:time.sleep(delay)
        f.seek(0);f.truncate();f.write(str(time.monotonic()));f.flush()
        fcntl.flock(f,fcntl.LOCK_UN)
def rpc(method,params,label=None):
    for retry in range(4):
        try:return _rpc_once(method,params,label)
        except RpcRateLimited:
            if retry==3:raise
            time.sleep(2**retry)
def _rpc_once(method, params, label=None):
    _pace_rpc()
    q = {'jsonrpc':'2.0','id':1,'method':method,'params':params}
    stamp = str(time.time_ns())
    try:
        with urllib.request.urlopen(urllib.request.Request(RPC,json.dumps(q).encode(),{'Content-Type':'application/json'}),timeout=30) as r:
            v = json.load(r)
    except Exception as e:
        message = str(e).replace(RPC, '[devnet RPC]')
        if RPC_SECRET: message = message.replace(RPC_SECRET, '[REDACTED]')
        save(EVIDENCE/(stamp+'-rpc-failure.json'), {'request':q,'error':message})
        if getattr(e,'code',None)==429:raise RpcRateLimited(message) from None
        raise RuntimeError(message) from None
    if label or 'error' in v:
        save(EVIDENCE/(stamp+'-'+(label or method)+'.json'), {'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'request':q,'response':v})
    if 'error' in v: raise RuntimeError(v['error'])
    return v['result']
def artifact(name):
    filename=CONFIG.get('artifact_files',{}).get(name,name+'.so')
    assert pathlib.Path(filename).name==filename
    return PRIVATE/'artifacts'/filename
def key_path(name):
    filename=CONFIG.get('key_files',{}).get(name,name+'.json')
    assert pathlib.Path(filename).name==filename
    return PRIVATE/'keys'/filename
def key(name):
    filename=CONFIG.get('key_files',{}).get(name,name+'.json')
    assert pathlib.Path(filename).name==filename
    k = Keypair.from_bytes(bytes(json.loads((PRIVATE/'keys'/filename).read_text())))
    assert str(k.pubkey()) == IDS[name]
    return k
class ExpiredTransaction(RuntimeError): pass
def pb(p): return bytes(Pubkey.from_string(p))
def meta(p,s=False,w=False): return {'key':p,'signer':s,'writable':w}
def ix(p, accounts, data): return {'program':p,'accounts':accounts,'data':base64.b64encode(data).decode()}
def build(instructions, blockhash, compute_limit=CU):
    # Stable first-seen order within each canonical permission category.
    flags = {IDS['payer']:[True,True]}
    for i in instructions:
        for a in i['accounts']+[meta(i['program'])]:
            f=flags.setdefault(a['key'],[False,False]); f[0] |= a['signer']; f[1] |= a['writable']
    keys = sorted(flags, key=lambda p:(not flags[p][0],not flags[p][1]))
    assert keys[0] == IDS['payer']
    signers=[p for p in keys if flags[p][0]]
    header=bytes([len(signers),sum(s and not w for s,w in flags.values()),sum(not s and not w for s,w in flags.values())])
    # priority fee occupies config mask bits 0 and 1; remaining fields bits 2..4.
    assert 0<compute_limit<=1_400_000
    message=b'\x81'+header+struct.pack('<I',31)+pb(blockhash)+bytes([len(instructions),len(keys)])+b''.join(map(pb,keys))+struct.pack('<QIII',10_000,compute_limit,8*1024*1024,256*1024)
    headers=[]; bodies=[]
    for i in instructions:
        data=base64.b64decode(i['data']); acc=bytes(keys.index(a['key']) for a in i['accounts'])
        headers.append(struct.pack('<BBH',keys.index(i['program']),len(acc),len(data))); bodies.append(acc+data)
    message+=b''.join(headers)+b''.join(bodies)
    names={v:k for k,v in IDS.items()}
    signatures=[key(names[p]).sign_message(message) for p in signers]
    wire=message+b''.join(bytes(s) for s in signatures)
    assert len(wire)<4096
    return wire,str(signatures[0]),message
def confirm(signature, path, status_hint=None):
    expiry=json.loads((path/'input.json').read_text())['blockhash']['lastValidBlockHeight']
    for attempt in range(90):
        status=status_hint if attempt==0 and status_hint is not None else rpc('getSignatureStatuses',[[signature],{'searchTransactionHistory':True}])['value'][0]
        if status is None and attempt%5==0:
            height=rpc('getBlockHeight',[{'commitment':'finalized'}])
            if height>expiry:
                assert rpc('getTransaction',[signature,{'encoding':'json','commitment':'finalized','maxSupportedTransactionVersion':1}]) is None
                save(path/'expired.json',{'signature':signature,'last_valid_block_height':expiry,'observed_finalized_block_height':height,'status':None,'transaction':None,'landed':False})
                raise ExpiredTransaction('Unlanded transaction expired: '+signature)
            if attempt in (5,10,15):
                wire=base64.b64encode((path/'signed-wire.bin').read_bytes()).decode()
                try:
                    result=rpc('sendTransaction',[wire,{'encoding':'base64','skipPreflight':False,'preflightCommitment':'finalized','maxRetries':20}],label='rebroadcast-exact-signed-bytes')
                    assert result==signature
                except RuntimeError:
                    # The RPC error is already preserved; resolve the same signature.
                    print('Rebroadcast response failed; preserving evidence and resolving the existing signature.',flush=True)
        if status and status['confirmationStatus']=='finalized':
            save(path/'status.json',status)
            assert status['err'] is None, status
            tx=rpc('getTransaction',[signature,{'encoding':'json','commitment':'finalized','maxSupportedTransactionVersion':1}])
            assert tx is not None
            save(path/'transaction.json',tx)
            assert tx['meta']['err'] is None
            save(path/'confirmed.json',{'signature':signature,'slot':tx['slot'],'fee':tx['meta']['fee'],'units_consumed':tx['meta'].get('computeUnitsConsumed'),'declared_cu':json.loads((path/'input.json').read_text())['declared_cu'],'wire_bytes':len((path/'signed-wire.bin').read_bytes()),'explorer':'https://explorer.solana.com/tx/'+signature+'?cluster=devnet'})
            print(json.dumps({'name':path.parent.name,**json.loads((path/'confirmed.json').read_text())}),flush=True)
            return tx
        time.sleep(2)
    raise RuntimeError('Confirmation timeout; preserve signed bytes and resolve signature before any retry: '+signature)
def transaction(name, instructions, submit=True, expect_error=False, wait=True, compute_limit=CU):
    root=EVIDENCE/name; root.mkdir(exist_ok=True)
    for previous in sorted(root.glob('attempt-*')):
        if (previous/'confirmed.json').exists():
            original=json.loads((previous/'input.json').read_text())
            assert original['instructions']==instructions and original['declared_cu']==compute_limit, 'A named phase cannot reuse a receipt for different inputs.'
            return json.loads((previous/'transaction.json').read_text())
        if (previous/'submitted.json').exists() and not (previous/'expired.json').exists():
            try:return confirm(json.loads((previous/'submitted.json').read_text())['signature'],previous)
            except ExpiredTransaction:pass
    if submit:assert len(list(root.glob('attempt-*')))<3, 'Bounded attempt limit reached; inspect preserved evidence before continuing.'
    path=root/('attempt-'+str(len(list(root.glob('attempt-*')))+1)); path.mkdir()
    blockhash=recent_blockhash(force=True)
    wire,signature,message=build(instructions,blockhash['blockhash'],compute_limit)
    (path/'signed-wire.bin').write_bytes(wire)
    save(path/'input.json',{'instructions':instructions,'blockhash':blockhash,'signature':signature,'sha256':hashlib.sha256(wire).hexdigest(),'declared_cu':compute_limit})
    encoded=base64.b64encode(wire).decode()
    sim=rpc('simulateTransaction',[encoded,{'encoding':'base64','sigVerify':True,'commitment':'finalized'}]);save(path/'simulation.json',sim)
    save(path/'fee.json',{'source':'exact signed transaction simulation','lamports':sim['value'].get('fee')})
    err=sim['value']['err']
    print(json.dumps({'name':name,'simulation_error':err,'units':sim['value'].get('unitsConsumed'),'bytes':len(wire)}),flush=True)
    if expect_error:
        assert err is not None
        return sim
    assert err is None, sim
    if not submit:return sim
    # Durable intent before sending: an uncertain RPC response must never trigger a duplicate settlement.
    save(path/'submitted.json',{'signature':signature,'exact_bytes_simulated_and_submitted':True})
    result=rpc('sendTransaction',[encoded,{'encoding':'base64','skipPreflight':False,'preflightCommitment':'finalized','maxRetries':20}])
    assert result==signature
    if not wait: return {'signature':signature,'path':str(path)}
    return confirm(signature,path)
def rent(n):return rpc('getMinimumBalanceForRentExemption',[n])
def create(name,owner,space):
    return ix(SYSTEM,[meta(IDS['payer'],True,True),meta(IDS[name],True,True)],struct.pack('<IQQ',0,rent(space),space)+pb(owner))
def gate():
    assert rpc('getGenesisHash',[],'genesis')==GENESIS
    v=rpc('getVersion',[],'version')
    a=rpc('getAccountInfo',['txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL',{'encoding':'base64','commitment':'finalized'}],'txv1-feature')
    assert a['value']['owner']=='Feature111111111111111111111111111111111111'
    b=base64.b64decode(a['value']['data'][0]);assert len(b)==9 and b[0]==1 and int.from_bytes(b[1:],'little')<a['context']['slot']
    return transaction('gate-v1-1200000',[ix(SYSTEM,[meta(IDS['payer'],True,True),meta(IDS['payer'],False,True)],struct.pack('<IQ',2,0))],submit=False)
def snapshot(name):
    keys=[PLAN['master'],*PLAN.get('receipts',[]),*PLAN['lanes'],*PLAN['pages'],PLAN['checkpoint'],PLAN['vault'],PLAN['registry'],PLAN['entry'],PLAN['nullifier_marker'],IDS['mint'],IDS['source'],IDS['proof'],IDS['payer']]
    r=rpc('getMultipleAccounts',[keys,{'encoding':'base64','commitment':'finalized'}])
    value={'slot':r['context']['slot'],'accounts':dict(zip(keys,r['value']))}
    save(EVIDENCE/(name+'.json'),value);return value
def assert_token_state(snapshot):
    a=snapshot['accounts'];total=PLAN['deposit_count']*1000
    mint=a[IDS['mint']];assert mint['owner']==TOKEN and not mint['executable']
    m=base64.b64decode(mint['data'][0]);assert len(m)==82
    assert m[:4]==struct.pack('<I',1) and m[4:36]==pb(IDS['source_authority'])
    assert struct.unpack('<Q',m[36:44])[0]==total and m[44:46]==bytes([0,1]) and m[46:50]==bytes(4)
    vault_authority=Pubkey.find_program_address([b'aspis-pool-vault-authority-v1',pb(PLAN['master'])],Pubkey.from_string(IDS['pool']))[0]
    for address,owner,amount in [(IDS['source'],pb(IDS['source_authority']),0),(PLAN['vault'],bytes(vault_authority),total)]:
        account=a[address];assert account['owner']==TOKEN and not account['executable']
        b=base64.b64decode(account['data'][0]);assert len(b)==165 and b[:32]==pb(IDS['mint']) and b[32:64]==owner
        assert struct.unpack('<Q',b[64:72])[0]==amount and b[108]==1
        assert b[72:76]==bytes(4) and b[109:113]==bytes(4) and b[121:133]==bytes(12)
    return {'mint_supply':total,'decimals':0,'source_balance':0,'vault_balance':total,'vault_authority':str(vault_authority),'mint_authority':IDS['source_authority']}
def setup():
    gate()
    transaction('token-initialize',[
        create('mint',TOKEN,82),ix(TOKEN,[meta(IDS['mint'],False,True)],bytes([20,0])+pb(IDS['source_authority'])+bytes([0])),
        create('source',TOKEN,165),ix(TOKEN,[meta(IDS['source'],False,True),meta(IDS['mint'])],bytes([18])+pb(IDS['source_authority'])),
        ix(TOKEN,[meta(IDS['mint'],False,True),meta(IDS['source'],False,True),meta(IDS['source_authority'],True)],bytes([7])+struct.pack('<Q',PLAN['deposit_count']*1000))])
    transaction('pool-initialize',[PLAN['initialize']])
    # Preserve fixed deposit order while fitting two supported instructions in 1.2M CU.
    for start in range(0,len(PLAN['deposits']),2):
        batch=PLAN['deposits'][start:start+2]
        transaction('deposit-batch-'+str(start),[item['instruction'] for item in batch])
    pending=[]
    for i,ins in enumerate(PLAN.get('checkpoint_preparations',[])):
        pending.append(transaction('checkpoint-validate-lane-'+str(i),[ins],wait=False))
    for item in pending:
        if 'signature' in item:confirm(item['signature'],pathlib.Path(item['path']))
    transaction('pool-checkpoint',[PLAN['checkpoint_instruction']])
    snapshot('initialized-state')
def registry():
    instructions=json.loads((HERE/'registry-plan.json').read_text())
    transaction('registry-initialize',[instructions['initialize']])
    scheduling=EVIDENCE/'registry-scheduling.json'
    if scheduling.exists():
        schedule=json.loads(scheduling.read_text())
    else:
        slot=rpc('getSlot',[{'commitment':'finalized'}])+200
        ins=instructions['schedule'];b=bytearray(base64.b64decode(ins['data']));b[120:128]=struct.pack('<Q',slot);ins['data']=base64.b64encode(b).decode()
        schedule={'activation_slot':slot,'instruction':ins};save(scheduling,schedule)
    transaction('registry-schedule',[schedule['instruction']])
    for poll in range(120):
        if rpc('getSlot',[{'commitment':'finalized'}])>=schedule['activation_slot']:break
        if poll%10==0:print('Waiting for the declared registry activation slot.',flush=True)
        time.sleep(2)
    else:raise RuntimeError('Registry activation slot not reached; preserve scheduled entry.')
    for name in ['activate','freeze']:transaction('registry-'+name,[instructions[name]])
    live=snapshot('authoritative-before-proof')
    save(EVIDENCE/'authoritative-token-assertions.json',assert_token_state(live))
def upload(name, data, prefix=''):
    assert name in ['proof','bad_proof']
    accounts=[meta(IDS[name],False,True),meta(IDS['authority'],True)]
    transaction(prefix+name+'-create',[create(name,IDS['verifier'],40+len(data)),ix(IDS['verifier'],[meta(IDS[name],True,True),accounts[1]],b'\0'+struct.pack('<I',len(data)))])
    pending=[]
    for offset in range(0,len(data),2800):
        chunk=data[offset:offset+2800]
        pending.append(transaction(prefix+name+'-upload-'+str(offset),[ix(IDS['verifier'],accounts,b'\x01'+struct.pack('<II',offset,len(chunk))+chunk)],wait=False))
        time.sleep(0.35)
    for item in pending:
        if 'signature' in item:confirm(item['signature'],pathlib.Path(item['path']))
    transaction(prefix+name+'-seal',[ix(IDS['verifier'],accounts,bytes([62]))])
    live=rpc('getAccountInfo',[IDS[name],{'encoding':'base64','commitment':'finalized'}])['value']
    assert live['owner']==IDS['verifier']
    assert base64.b64decode(live['data'][0])==b'ASPU'+struct.pack('<I',len(data))+bytes(32)+data
    save(EVIDENCE/(prefix+name+'-sealed.json'),{'account':IDS[name],'payload_bytes':len(data),'account_bytes':40+len(data),'sha256':hashlib.sha256(data).hexdigest(),'onchain_exact_match':True})
if __name__=='__main__':
    mode=sys.argv[1]
    if mode=='gate':gate()
    elif mode=='setup':setup()
    elif mode=='registry':registry()
    elif mode=='snapshot':snapshot(sys.argv[2])
    elif mode=='upload':upload(sys.argv[2],pathlib.Path(sys.argv[3]).read_bytes())
    elif mode=='terminal':
        before=snapshot('before-settlement')
        transaction('atomic-transfer',[json.loads((PRIVATE/'context/terminal.json').read_text())])
        snapshot('after-settlement')
    else:raise ValueError(mode)
