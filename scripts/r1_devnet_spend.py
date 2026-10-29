#!/usr/bin/env python3
"""Config-driven R1 devnet setup and spends; wallet files stay in retained host private directories.
Run inside r1_devnet_receipt.sh and the documented capped scope.
"""
import base64,json,os,pathlib,subprocess,sys,time,hashlib,re
from concurrent.futures import ThreadPoolExecutor
from r1_devnet_rpc import rpc
from r1_devnet_policy import require_key, created_accounts, state_rent
from Client64_proof_accounts import proof_plan, retain_key, key_public
C=json.load(open(sys.argv[1]));O=pathlib.Path(sys.argv[2]);O.mkdir(exist_ok=True,mode=0o700)
URL=C['rpc_url'];SIGNER=C.get('signer','native-target/release/devnet_spend')
CLI=pathlib.Path(C.get('cli_dir',str(pathlib.Path.home()/'.local/share/solana/install/active_release/bin')))
KEYS=pathlib.Path(C.get('key_dir','keys'));PAYER_KEY=str(C.get('payer_key',KEYS/'payer.json'))
SYSTEM='11111111111111111111111111111111';TOKEN='TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA'
def write(name,v):
    p=O/(name+'.json');p.write_text(json.dumps(v,indent=2)+'\n')
def key(name,require_existing=False):
    namespace=C.get('key_namespace','')
    assert re.fullmatch(r'[A-Za-z0-9_-]*',namespace), 'invalid key namespace'
    p=pathlib.Path(C.get('key_dir','keys'))/((namespace+'-' if namespace else '')+name+'.json')
    if require_existing and not p.exists():raise RuntimeError('missing retained key; manual recovery required: '+str(p))
    if not p.exists():subprocess.run([str(CLI/'solana-keygen'),'new','--no-bip39-passphrase','--silent','-o',str(p)],stdout=subprocess.DEVNULL,check=True)
    os.chmod(p,0o600)
    return str(p),subprocess.check_output([str(CLI/'solana-keygen'),'pubkey',str(p)],text=True).strip()
def account(address):
    a=rpc(URL,'getAccountInfo',[address,{'encoding':'base64','commitment':'finalized'}])
    return a

def record_rent(transaction):
    addresses=created_accounts(transaction)
    if not addresses:return
    path=O/'rent-ledger.json'
    rows={row['address']:row for row in json.loads(path.read_text())} if path.exists() else {}
    for address in addresses:
        value=account(address)['value']
        if value:rows[address]=state_rent(address,value,C['payer'],globals().get('gov'))
    write('rent-ledger',list(rows.values()))
def invoke(q):return json.loads(subprocess.check_output([SIGNER],input=json.dumps(q).encode()))
def send(name,ixs,keys=[PAYER_KEY],negative=False):
    done=O/(name+'.json')
    if done.exists():
        old=json.load(open(done))
        if old.get('finalized'):
            if bool(old['error'])!=negative:raise RuntimeError(f'{name}: prior finalized result had an unexpected error')
            return old
        raise RuntimeError(f'{name}: prior incomplete transaction; inspect attempt signatures before resuming')
    prior=[]
    for path in O.glob(name+'-attempt-*.json'):
        if re.fullmatch(re.escape(name)+r'-attempt-[0-9]+\.json',path.name):prior.append((path,json.load(open(path))))
    for path,attempt_record in sorted(prior):
        sig=attempt_record['signature']
        while True:
            status=rpc(URL,'getSignatureStatuses',[[sig],{'searchTransactionHistory':True}])['value'][0]
            if status and status['confirmationStatus']=='finalized':
                tx=rpc(URL,'getTransaction',[sig,{'encoding':'json','commitment':'finalized','maxSupportedTransactionVersion':1}])
                if not tx:raise RuntimeError(f'{name}: finalized metadata not yet available')
                write(name+'-transaction',tx);record_rent(tx)
                origin=attempt_record.get('started_unix',path.stat().st_mtime)
                result={'signature':sig,'explorer':(None if URL.startswith(('http://127.0.0.1:','http://localhost:')) else f'https://explorer.solana.com/tx/{sig}?cluster=devnet'),'slot':tx['slot'],'compute_units':tx['meta'].get('computeUnitsConsumed'),'fee':tx['meta']['fee'],'error':tx['meta']['err'],'wall_seconds':time.time()-origin,'wall_seconds_kind':'reconciled_since_signed_receipt','serialized_bytes':attempt_record['serialized_bytes'],'finalized':True,'negative':negative,'reconciled':True}
                write(name,result)
                if bool(result['error'])!=negative:raise RuntimeError(f'{name}: reconciled unexpected result {result}')
                print(name,json.dumps(result),flush=True);return result
            if status is None and rpc(URL,'getBlockHeight',[{'commitment':'finalized'}])>attempt_record['blockhash']['lastValidBlockHeight']:
                write(path.stem+'-expired',{'signature':sig,'expired_unlanded':True});break
            time.sleep(2)
    if not prior and list(O.glob(name+'-attempt-*.json')):
        raise RuntimeError(f'{name}: prior simulation-only failure requires inspection before resuming')
    start=time.monotonic()
    started_unix=time.time()
    first_attempt=1+max((int(path.stem.rsplit('-',1)[1]) for path,_ in prior),default=-1)
    for attempt in range(first_attempt,3):
        bh=rpc(URL,'getLatestBlockhash',[{'commitment':'confirmed'}])['value']
        signed=invoke({'keys':keys,'instructions':ixs,'blockhash':bh['blockhash']})
        wire=base64.b64encode(bytes.fromhex(signed['hex'])).decode();sig=signed['signature']
        simulation=rpc(URL,'simulateTransaction',[wire,{'encoding':'base64','sigVerify':True,'commitment':'confirmed'}]);write(f'{name}-attempt-{attempt}-simulation',simulation)
        simerr=simulation['value']['err']
        if simerr=='BlockhashNotFound':continue
        if bool(simerr)!=negative:raise RuntimeError(f'{name} unexpected simulation: {simulation}')
        write(f'{name}-attempt-{attempt}',{'signature':sig,'blockhash':bh,'simulation_error':simerr,'serialized_bytes':signed['bytes'],'started_unix':started_unix})
        try:
            sent=rpc(URL,'sendTransaction',[wire,{'encoding':'base64','skipPreflight':negative,'maxRetries':5,'preflightCommitment':'confirmed'}]);assert sent==sig
        except Exception as e:
            write(f'{name}-attempt-{attempt}-send-error',{'error':str(e)})
        while True:
            status=rpc(URL,'getSignatureStatuses',[[sig],{'searchTransactionHistory':True}])['value'][0]
            if status and status['confirmationStatus']=='finalized':break
            if not status and rpc(URL,'getBlockHeight',[{'commitment':'finalized'}])>bh['lastValidBlockHeight']:break
            time.sleep(2)
        if not status:continue
        tx=None
        for _ in range(10):
            tx=rpc(URL,'getTransaction',[sig,{'encoding':'json','commitment':'finalized','maxSupportedTransactionVersion':1}])
            if tx:break
            time.sleep(2)
        if not tx:raise RuntimeError('finalized tx metadata unavailable')
        write(name+'-transaction',tx);record_rent(tx)
        result={'signature':sig,'explorer':(None if URL.startswith(('http://127.0.0.1:','http://localhost:')) else f'https://explorer.solana.com/tx/{sig}?cluster=devnet'),'slot':tx['slot'],'compute_units':tx['meta'].get('computeUnitsConsumed'),'fee':tx['meta']['fee'],'error':tx['meta']['err'],'wall_seconds':time.monotonic()-start,'serialized_bytes':signed['bytes'],'finalized':True,'negative':negative}
        write(name,result)
        if bool(result['error'])!=negative:raise RuntimeError(f'{name} unexpected finalized result: {result}')
        print(name,json.dumps(result),flush=True);return result
    raise RuntimeError(f'{name}: blockhash expiry attempt cap reached')
def ix(program,accounts,data):return {'program':program,'accounts':accounts,'data':data.hex()}
def create(name,address,owner,size,signer):
    existing=account(address)['value']
    if existing is not None:
        assert existing['owner']==owner and not existing['executable'] and len(base64.b64decode(existing['data'][0]))==size, f'{name}: unexpected existing account'
        return
    rent=rpc(URL,'getMinimumBalanceForRentExemption',[size])
    data=(0).to_bytes(4,'little')+rent.to_bytes(8,'little')+size.to_bytes(8,'little')+b58(owner)
    return send(name,[ix(SYSTEM,[[C['payer'],True,True],[address,True,True]],data)],[PAYER_KEY,signer])
def b58(s):
    alphabet='123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';n=0
    for x in s:n=n*58+alphabet.index(x)
    return b'\0'*(len(s)-len(s.lstrip('1')))+n.to_bytes((n.bit_length()+7)//8,'big')
def plan(action,**kw):return invoke({**C['programs'],'payer':C['payer'],'mint':mint,'action':action,**kw})
def readhex(address,owner):
    a=account(address);assert a['value'] and a['value']['owner']==owner and not a['value']['executable']
    return base64.b64decode(a['value']['data'][0]).hex()
def upload(label,address,path,body):
    timing_file=O/(label+'-phase-timing.json')
    if timing_file.exists():timing=json.load(open(timing_file))
    else:
        earlier=list(O.glob(label+'-*-attempt-*.json'))
        timing={'started_unix':min(p.stat().st_mtime for p in earlier) if earlier else time.time(),'origin_kind':'first_legacy_receipt_mtime' if earlier else 'phase_entry'}
        write(label+'-phase-timing',timing)
    def one(item):
        i,start=item;time.sleep((i%4)*.25)
        return send(f'{label}-{i}',[ix(C['carrier'],[[address,True,True]],start.to_bytes(4,'little')+body[start:start+3763])],[PAYER_KEY,path])
    # Disjoint ranges may be submitted concurrently. Every transaction must
    # finalize before byte readback or stage 1; at most four are in flight.
    with ThreadPoolExecutor(max_workers=4) as pool:
        stats=list(pool.map(one,enumerate(range(0,len(body),3763))))
    actual=bytes.fromhex(readhex(address,C['carrier']));assert actual==body
    result={'count':len(stats),'compute_units':sum(s['compute_units'] for s in stats),'wall_seconds':time.time()-timing['started_unix'],'wall_origin_kind':timing['origin_kind'],'transaction_wall_seconds_sum':sum(s['wall_seconds'] for s in stats),'sha256':hashlib.sha256(body).hexdigest()};write(label+'-summary',result);return result

write('retained-payer',require_key(PAYER_KEY,CLI,C['payer']))
assert rpc(URL,'getGenesisHash',[])==C['genesis_hash']
assert 'carrier' in C,'deploy and pin the raw-buffer carrier before setup'
if (O/'complete.json').exists():
    completed=json.load(open(O/'complete.json'));assert completed['programs']==C['programs'] and completed['payer']==C['payer']
    print('Recorded run already complete; use a fresh key_namespace and receipt directory for a new run.');sys.exit(0)
mintkey,mint=key('spend-mint');sourcekey,source=key('spend-source');destkey,dest=key('spend-destination');govkey,gov=key('spend-governance')
if C.get('mint'):assert C['mint']==mint, 'retained mint key does not match public config'
for role,actual in [('source',source),('destination',dest),('token_owner',gov)]:
    if role in C.get('accounts',{}):assert C['accounts'][role]==actual
# This demonstration deliberately uses public fixture note witnesses; it measures R1, not wallet secrecy.
create('mint-create',mint,TOKEN,82,mintkey)
if not (O/'mint-initialize.json').exists():send('mint-initialize',[ix(TOKEN,[[mint,False,True]],bytes([20,6])+b58(C['payer'])+bytes([0]))])
for label,address,path in [('source',source,sourcekey),('destination',dest,destkey)]:
    create(label+'-create',address,TOKEN,165,path)
    send(label+'-initialize',[ix(TOKEN,[[address,False,True],[mint,False,False]],bytes([18])+b58(gov))])
send('mint-supply',[ix(TOKEN,[[mint,False,True],[source,False,True],[C['payer'],True,False]],bytes([7])+(2000).to_bytes(8,'little'))])
write('mint-setup',{'mint':mint,'source':source,'destination':dest,'token_owner':gov,'mint_authority':C['payer'],'decimals':6,'supply_base_units':2000})
if '--mint-only' in sys.argv:sys.exit(0)
slot=rpc(URL,'getSlot',[{'commitment':'finalized'}]);setupfile=O/'setup-plan.json'
if setupfile.exists():setup=json.load(open(setupfile))
else:
    setup=plan('setup',funding_payer=C['payer'],governance=gov,activation_slot=slot+100,registry_hash=C['release_artifacts']['registry']['sha256'],verifier_hash=C['release_artifacts']['devnet_verifier']['sha256']);write('setup-plan',setup)
if not C.get('pool_initialize_after_registry',False):send('pool-initialize',[setup['initialize']])
send('registry-initialize',[setup['registry_initialize']],[PAYER_KEY,govkey])
if not (O/'registry-schedule.json').exists():
    activation=rpc(URL,'getSlot',[{'commitment':'confirmed'}])+100
    setup=plan('setup',funding_payer=C['payer'],governance=gov,activation_slot=activation,registry_hash=C['release_artifacts']['registry']['sha256'],verifier_hash=C['release_artifacts']['devnet_verifier']['sha256']);setup['activation_slot']=activation;write('setup-plan',setup)
send('registry-schedule',[setup['schedule']],[PAYER_KEY,govkey])
while rpc(URL,'getSlot',[{'commitment':'finalized'}])<setup['activation_slot']:time.sleep(2)
send('registry-activate',[setup['activate']],[PAYER_KEY,govkey])
send('registry-freeze',[setup['freeze']],[PAYER_KEY,govkey])
if C.get('pool_initialize_after_registry',False):send('pool-initialize',[setup['initialize']])
deposits=[]
for n in range(2):
    d=plan('deposit',note=n,source=source,token_owner=gov,genesis=True)
    # The second note may land in the same lane; then use its existing root page.
    if account(d['page'])['value'] is not None:d=plan('deposit',note=n,source=source,token_owner=gov,genesis=False)
    write(f'deposit-{n}-plan',d);send(f'deposit-{n}',[d['instruction']],[PAYER_KEY,govkey]);deposits.append(d)
cp=plan('checkpoint',sequence=0);send('forest-checkpoint',[cp['instruction']]);write('forest-checkpoint-plan',cp)
for n,label in enumerate(['transfer','withdrawal']):
    saved=O/(label+'-proof-plan.json')
    resuming=(O.joinpath(C.get('proof_key_dir',''))/((C.get('key_namespace','')+'-' if C.get('key_namespace') else '')+label+'-client64-proof-private')).exists() or saved.exists()
    publickey,publicaccount=key(label+'-public',require_existing=resuming);cpkey,verifiercp=key(label+'-checkpoint',require_existing=resuming)
    identity={**C['programs'],'payer':C['payer'],'mint':mint,'action':'prove',
              'note':n,'withdrawal':n==1,'destination':dest,'checkpoint':cp['checkpoint'],
              'public_account':publicaccount,'verifier_checkpoint':verifiercp}
    p,proofkey=proof_plan(O.joinpath(C.get('proof_key_dir',''))/((C.get('key_namespace','')+'-' if C.get('key_namespace') else '')+label+'-client64-proof-private'),identity,
        lambda: {'lane_bytes':readhex(deposits[n]['output_lane'],C['programs']['pool']),
                 'checkpoint_bytes':readhex(cp['checkpoint'],C['programs']['pool'])},
        invoke,lambda address: account(address)['value'] is None,
        lambda path: retain_key(path,CLI),lambda path: key_public(path,CLI),saved)
    proofaccount=p['proof_account'];write(label+'-proof-plan',p)
    proofdir=O.joinpath(C.get('proof_key_dir',''))/((C.get('key_namespace','')+'-' if C.get('key_namespace') else '')+label+'-client64-proof-private')/'proof'
    proof=(proofdir/'proof.bin').read_bytes();public=(proofdir/'statement.bin').read_bytes()
    create(label+'-proof-create',proofaccount,C['carrier'],len(proof),proofkey);create(label+'-public-create',publicaccount,C['carrier'],len(public),publickey)
    t=time.monotonic();proof_stats=upload(label+'-proof-upload',proofaccount,proofkey,proof);statement_stats=upload(label+'-statement-upload',publicaccount,publickey,public)
    assert (proof_stats['count'],statement_stats['count'])==(16,1), 'frozen upload count changed'
    write(label+'-uploads-phase',{'wall_seconds':proof_stats['wall_seconds']+statement_stats['wall_seconds'],'wall_origin_kind':proof_stats['wall_origin_kind'],'proof_count':proof_stats['count'],'statement_count':statement_stats['count'],'compute_units':proof_stats['compute_units']+statement_stats['compute_units']})
    create(label+'-checkpoint-create',verifiercp,C['programs']['verifier'],1768,cpkey)
    send(label+'-stage1',[p['stage1']]);send(label+'-stage2',[p['settle']])
    readback={a:account(a) for a in [p['marker'],p['output_lane'],setup['vault'],dest,verifiercp]};write(label+'-readback',readback)
    assert readback[p['marker']]['value'] is not None,'settled nullifier marker missing'
    validation=plan('validate_settlement',note=n,lane_bytes=base64.b64decode(readback[p['output_lane']]['value']['data'][0]).hex(),marker_bytes=base64.b64decode(readback[p['marker']]['value']['data'][0]).hex(),candidate_bytes=proof[:-57607].hex());write(label+'-settlement-validation',validation)
    vault_amount=int.from_bytes(base64.b64decode(readback[setup['vault']]['value']['data'][0])[64:72],'little')
    destination_amount=int.from_bytes(base64.b64decode(readback[dest]['value']['data'][0])[64:72],'little')
    assert (vault_amount,destination_amount)==((2000,0) if n==0 else (1750,250)), 'settlement SPL balance mismatch'
    write(label+'-token-balances',{'vault':vault_amount,'destination':destination_amount})
    replay=send(label+'-replay',[p['settle']],negative=True)
    assert replay['error']=={'InstructionError':[0,{'Custom':0x41532026}]},'replay did not reject as NullifierAlreadyConsumed'
    after_replay={a:account(a) for a in readback}
    assert all(readback[a]['value']==after_replay[a]['value'] for a in readback),'replay changed protected state'
    write(label+'-replay-validation',{'error_name':'NullifierAlreadyConsumed','custom_code':0x41532026,'protected_accounts_unchanged':True})
    negkey,negcp=key(label+'-negative-checkpoint');create(label+'-negative-checkpoint-create',negcp,C['programs']['verifier'],1768,negkey)
    # Mutate the compact proof header, leaving candidate bytes intact, and use a fresh checkpoint.
    offset=len(proof)-57607
    send(label+'-mutate-proof',[ix(C['carrier'],[[proofaccount,True,True]],offset.to_bytes(4,'little')+bytes([proof[offset]^1]))],[PAYER_KEY,proofkey])
    negstage=json.loads(json.dumps(p['stage1']));negstage['accounts'][2][0]=negcp
    negative_before=account(negcp)['value']
    mutation=send(label+'-mutated-stage1',[negstage],negative=True)
    assert mutation['error']=={'InstructionError':[0,'InvalidInstructionData']},'mutated proof failed for an unexpected reason'
    assert account(negcp)['value']==negative_before,'mutated proof changed zero checkpoint'
    write(label+'-mutation-validation',{'error_name':'InvalidInstructionData','fresh_checkpoint_unchanged':True})
    send(label+'-restore-proof',[ix(C['carrier'],[[proofaccount,True,True]],offset.to_bytes(4,'little')+proof[offset:offset+1])],[PAYER_KEY,proofkey])
created=set()
for receipt in O.glob('*-transaction.json'):
    created.update(created_accounts(json.loads(receipt.read_text())))
ledger=[]
for address in sorted(created):
    current=account(address)['value']
    if current:ledger.append(state_rent(address,current,C['payer'],gov))
write('rent-ledger',ledger)
write('complete',{'settled':['transfer','withdrawal'],'negative_checks':['transfer-replay','withdrawal-replay','transfer-mutated-stage1','withdrawal-mutated-stage1'],'mint':mint,'source':source,'destination':dest,'fixture_witnesses_public':True,'programs':C['programs'],'payer':C['payer'],'key_namespace':C.get('key_namespace','')})
