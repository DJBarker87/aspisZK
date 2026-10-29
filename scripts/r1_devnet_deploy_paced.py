#!/usr/bin/env python3
"""Paced deployment with retained buffer keys, byte readback and receipts."""
import base64,hashlib,json,os,pathlib,subprocess,sys,time,signal
from r1_devnet_rpc import rpc
from r1_devnet_release_gate import base58
from r1_devnet_policy import require_key, loader_rent, close_failed_buffer
C=json.load(open(sys.argv[1]));O=pathlib.Path(sys.argv[2]);O.mkdir(exist_ok=False,mode=0o700)
URL=C['rpc_url'];CLI=pathlib.Path(C.get('cli_dir',str(pathlib.Path.home()/'.local/share/solana/install/active_release/bin')))
KEYS=pathlib.Path(C.get('key_dir','keys'));PAYER_KEY=str(C.get('payer_key',KEYS/'payer.json'));SIGNER=C.get('signer','native-target/release/devnet_spend')
LOADER='BPFLoaderUpgradeab1e11111111111111111111111';SYSTEM='11111111111111111111111111111111'
def pub(path):return subprocess.check_output([str(CLI/'solana-keygen'),'pubkey',str(path)],text=True).strip()
def write(name,v):(O/(name+'.json')).write_text(json.dumps(v,indent=2)+'\n')
def account(key):return rpc(URL,'getAccountInfo',[key,{'encoding':'base64','commitment':'finalized'}])
def signed(ixs,keys,bh):
    q={'keys':keys,'blockhash':bh,'instructions':ixs};return json.loads(subprocess.check_output([SIGNER],input=json.dumps(q).encode()))
def ix(program,accounts,data):return {'program':program,'accounts':accounts,'data':data.hex()}
def wait(batch,allow_error=False):
    begin=time.monotonic()
    while True:
        status=rpc(URL,'getSignatureStatuses',[[x['signature'] for x in batch],{'searchTransactionHistory':True}])['value']
        if allow_error and any(s is None for s in status):
            height=rpc(URL,'getBlockHeight',[{'commitment':'finalized'}])
            for i,(entry,state) in enumerate(zip(batch,status)):
                expiry=entry.get('blockhash',{}).get('lastValidBlockHeight')
                if state is None and expiry is not None and height>expiry:
                    status[i]={'confirmationStatus':'expired_unlanded','err':None}
        if all(s and s['confirmationStatus'] in ('finalized','expired_unlanded') for s in status):break
        if time.monotonic()-begin>100:raise RuntimeError('batch finalization timeout; inspect signatures before restarting')
        time.sleep(2)
    for e,s in zip(batch,status):
        e.update(s)
        if s['confirmationStatus']=='expired_unlanded':continue
        tx=rpc(URL,'getTransaction',[e['signature'],{'encoding':'json','commitment':'finalized','maxSupportedTransactionVersion':1}]);write('tx-'+e['signature'],tx)
        if s['err'] and not allow_error:raise RuntimeError(s)
def submit(name,ixs,keys,bh):
    t=time.monotonic()
    for attempt in range(3):
        # Bulk RPC throttling can consume a batch's blockhash lifetime. Each
        # individual write gets a new hash, and every signed attempt is retained.
        block=rpc(URL,'getLatestBlockhash',[{'commitment':'confirmed'}])['value']
        s=signed(ixs,keys,block['blockhash']);wire=base64.b64encode(bytes.fromhex(s['hex'])).decode()
        sim=rpc(URL,'simulateTransaction',[wire,{'encoding':'base64','sigVerify':True,'commitment':'confirmed'}]);write(f'{name}-attempt-{attempt}-simulation',sim)
        if sim['value']['err']=='BlockhashNotFound':continue
        if sim['value']['err']:raise RuntimeError(sim)
        entry={'signature':s['signature'],'blockhash':block,'serialized_bytes':s['bytes'],'explorer':f"https://explorer.solana.com/tx/{s['signature']}?cluster=devnet"};write(f'{name}-attempt-{attempt}',entry)
        try:
            sig=rpc(URL,'sendTransaction',[wire,{'encoding':'base64','skipPreflight':False,'maxRetries':5,'preflightCommitment':'confirmed'}]);assert sig==s['signature']
        except Exception as error:
            write(f'{name}-attempt-{attempt}-error',{'error':str(error)})
            if 'Blockhash not found' in str(error):continue  # preflight rejected; not submitted
            while True:
                status=rpc(URL,'getSignatureStatuses',[[s['signature']],{'searchTransactionHistory':True}])['value'][0]
                if status:break
                if rpc(URL,'getBlockHeight',[{'commitment':'finalized'}])>block['lastValidBlockHeight']:break
                time.sleep(2)
            if not status:continue
        entry['submit_wall_seconds']=time.monotonic()-t;write(name,entry);return entry
    raise RuntimeError(f'{name}: blockhash retry cap')
roles=sys.argv[3:] or ['verifier','pool','registry','carrier']
write('retained-keys',[require_key(PAYER_KEY,CLI,C['payer'])]+[require_key(KEYS/(role+'.json'),CLI,C['programs'].get(role,C.get(role))) for role in roles])
assert rpc(URL,'getGenesisHash',[])==C['genesis_hash']
def deploy_role(role):
    started=time.monotonic();spec=C['release_artifacts']['devnet_verifier' if role=='verifier' else role];elf=pathlib.Path(spec['path']).read_bytes();assert hashlib.sha256(elf).hexdigest()==spec['sha256']
    program=C['programs'].get(role,C.get(role));assert program
    assert pub(str(KEYS/(role+'.json')))==program
    if account(program)['value']:raise RuntimeError(f'{role} exists; inspect instead of redeploying')
    path=KEYS/(role+'-deploy-buffer.json')
    if not path.exists():subprocess.run([str(CLI/'solana-keygen'),'new','--no-bip39-passphrase','--silent','-o',str(path)],stdout=subprocess.DEVNULL,check=True)
    os.chmod(path,0o600);buf=pub(path);ba=account(buf)['value'];sigs=[]
    if ba is None:
        size=len(elf)+37;rent=rpc(URL,'getMinimumBalanceForRentExemption',[size]);bh=rpc(URL,'getLatestBlockhash',[{'commitment':'confirmed'}])['value']['blockhash']
        create=(0).to_bytes(4,'little')+rent.to_bytes(8,'little')+size.to_bytes(8,'little')+base58(LOADER)
        e=submit(role+'-buffer-create',[ix(SYSTEM,[[C['payer'],True,True],[buf,True,True]],create),ix(LOADER,[[buf,False,True],[C['payer'],False,False]],bytes(4))],[PAYER_KEY,str(path)],bh);wait([e]);sigs.append(e);ba=account(buf)['value']
    assert ba['owner']==LOADER and not ba['executable']
    body=base64.b64decode(ba['data'][0])[37:];assert len(body)==len(elf)
    pending=[i for i in range(0,len(elf),900) if body[i:i+900]!=elf[i:i+900]];write(role+'-plan',{'buffer':buf,'missing_chunks':len(pending),'sha256':spec['sha256']})
    for first in range(0,len(pending),60):
        bh=rpc(URL,'getLatestBlockhash',[{'commitment':'confirmed'}])['value']['blockhash'];batch=[]
        for offset in pending[first:first+60]:
            chunk=elf[offset:offset+900];data=(1).to_bytes(4,'little')+offset.to_bytes(4,'little')+len(chunk).to_bytes(8,'little')+chunk
            e=submit(f'{role}-write-{offset}',[ix(LOADER,[[buf,False,True],[C['payer'],True,False]],data)],[PAYER_KEY],bh);e['offset']=offset;sigs.append(e);batch.append(e);write(role+'-signatures',sigs);time.sleep(C.get('write_delay_seconds',.2))
        wait(batch);write(role+'-signatures',sigs);print(f'{role}: {first+len(batch)}/{len(pending)} repaired',flush=True)
    body=base64.b64decode(account(buf)['value']['data'][0])[37:];assert body==elf;write(role+'-buffer-verified',{'sha256':hashlib.sha256(body).hexdigest(),'bytes':len(body),'slot':account(buf)['context']['slot']})
    cmd=[str(CLI/'solana'),'--url',URL,'--keypair',PAYER_KEY,'--commitment','finalized','--output','json','program','deploy',spec['path'],'--program-id',str(KEYS/(role+'.json')),'--buffer',str(path),'--max-len',str(len(elf)),'--use-rpc','--max-sign-attempts','2'];write(role+'-deploy-command',cmd)
    with open(O/(role+'-deploy.json'),'w') as stdout,open(O/(role+'-deploy-stderr.txt'),'w') as stderr:status=subprocess.run(cmd,stdout=stdout,stderr=stderr).returncode
    if status:raise RuntimeError(f'{role} deploy CLI exit {status}')
    pa=account(program);assert pa['value']['owner']==LOADER and pa['value']['executable'];raw=base64.b64decode(pa['value']['data'][0]);assert int.from_bytes(raw[:4],'little')==2
    # Programdata address encoded in the linked Program account; use the CLI public account output for its base58 form.
    show=subprocess.check_output([str(CLI/'solana'),'--url',URL,'--output','json','program','show',program],text=True);show=json.loads(show);write(role+'-program',show)
    pd=show['programdataAddress'];assert raw[4:36]==base58(pd);pda=account(pd);assert pda['value']['owner']==LOADER and not pda['value']['executable'] and int.from_bytes(base64.b64decode(pda['value']['data'][0])[:4],'little')==3;payload=base64.b64decode(pda['value']['data'][0])[45:];assert payload==elf
    write(role+'-programdata',{'address':pd,'lamports':pda['value']['lamports'],'bytes':len(payload)+45,'elf_sha256':hashlib.sha256(payload).hexdigest(),'context_slot':pda['context']['slot']})
    if role in ('verifier','registry'):
        # V2 certifies exactly an immutable loader deployment; required by this release.
        final=[str(CLI/'solana'),'--url',URL,'--keypair',PAYER_KEY,'--commitment','finalized','--output','json','program','set-upgrade-authority',program,'--final']
        with open(O/(role+'-immutable.json'),'w') as stdout,open(O/(role+'-immutable-stderr.txt'),'w') as stderr:subprocess.run(final,stdout=stdout,stderr=stderr,check=True)
        finaldata=base64.b64decode(account(pd)['value']['data'][0]);assert finaldata[12]==0 and finaldata[45:]==elf
    write(role+'-rent-ledger',[loader_rent(program,account(program)['value'],C['payer']),loader_rent(pd,account(pd)['value'],C['payer'])]);write(role+'-complete',{'program':program,'buffer':buf,'wall_seconds':time.monotonic()-started,'key_retained':True});print(role+' deployment verified',flush=True)

def interrupted(signum,frame):raise KeyboardInterrupt(f'interrupted by signal {signum}')
signal.signal(signal.SIGTERM,interrupted)
for role in roles:
    try:
        deploy_role(role)
    except BaseException:
        path=KEYS/(role+'-deploy-buffer.json')
        if path.exists():
            buffer=pub(path)
            # Finalization wait reconciles all retained submitted signatures. On
            # ambiguity it fails closed and keeps the buffer/key for recovery.
            records=[]
            for receipt in O.glob(role+'-*-attempt-*.json'):
                value=json.loads(receipt.read_text())
                if isinstance(value,dict) and value.get('signature'):records.append(value)
            for first in range(0,len(records),256):wait(records[first:first+256],allow_error=True)
            write(role+'-failure-refund',close_failed_buffer(CLI,URL,PAYER_KEY,C['payer'],buffer,account,lambda n,v:write(role+'-'+n,v)))
            write(role+'-refund-signatures',rpc(URL,'getSignaturesForAddress',[buffer,{'commitment':'finalized','limit':10}]))
        raise
    finally:
        command=[str(CLI/'solana'),'--url',URL,'--output','json','program','show','--buffers','--buffer-authority',C['payer']]
        result=subprocess.run(command,text=True,capture_output=True)
        write(role+'-final-buffers',{'command':command,'exit':result.returncode,'stdout':result.stdout,'stderr':result.stderr})
        if result.returncode:raise RuntimeError('buffer inventory failed; retain all keys')
        inventory=json.loads(result.stdout)
        entries=inventory.get('buffers',[]) if isinstance(inventory,dict) else inventory
        if entries:raise RuntimeError('buffers remain; inspect retained keys and receipts')
