#!/usr/bin/env python3
"""Paced deployment with retained buffer keys, byte readback and receipts."""
import base64,hashlib,json,os,pathlib,subprocess,sys,time
from r1_devnet_rpc import rpc
from r1_devnet_release_gate import base58
C=json.load(open(sys.argv[1]));O=pathlib.Path(sys.argv[2]);O.mkdir(exist_ok=False,mode=0o700)
URL=C['rpc_url'];CLI=pathlib.Path.home()/'.local/share/solana/install/active_release/bin'
LOADER='BPFLoaderUpgradeab1e11111111111111111111111';SYSTEM='11111111111111111111111111111111'
def pub(path):return subprocess.check_output([str(CLI/'solana-keygen'),'pubkey',str(path)],text=True).strip()
def write(name,v):(O/(name+'.json')).write_text(json.dumps(v,indent=2)+'\n')
def account(key):return rpc(URL,'getAccountInfo',[key,{'encoding':'base64','commitment':'finalized'}])
def signed(ixs,keys,bh):
    q={'keys':keys,'blockhash':bh,'instructions':ixs};return json.loads(subprocess.check_output(['native-target/release/devnet_spend'],input=json.dumps(q).encode()))
def ix(program,accounts,data):return {'program':program,'accounts':accounts,'data':data.hex()}
def wait(batch):
    begin=time.monotonic()
    while True:
        status=rpc(URL,'getSignatureStatuses',[[x['signature'] for x in batch],{'searchTransactionHistory':True}])['value']
        if all(s and s['confirmationStatus']=='finalized' for s in status):break
        if time.monotonic()-begin>100:raise RuntimeError('batch finalization timeout; inspect signatures before restarting')
        time.sleep(2)
    for e,s in zip(batch,status):
        e.update(s)
        if s['err']:raise RuntimeError(s)
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
        entry={'signature':s['signature'],'serialized_bytes':s['bytes'],'explorer':f"https://explorer.solana.com/tx/{s['signature']}?cluster=devnet"};write(f'{name}-attempt-{attempt}',entry)
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
assert pub('keys/payer.json')==C['payer']
assert rpc(URL,'getGenesisHash',[])==C['genesis_hash']
for role in sys.argv[3:] or ['verifier','pool','registry','carrier']:
    started=time.monotonic();spec=C['release_artifacts']['devnet_verifier' if role=='verifier' else role];elf=pathlib.Path(spec['path']).read_bytes();assert hashlib.sha256(elf).hexdigest()==spec['sha256']
    program=C['programs'].get(role,C.get(role));assert program
    assert pub(f'keys/{role}.json')==program
    if account(program)['value']:raise RuntimeError(f'{role} exists; inspect instead of redeploying')
    path=pathlib.Path('keys')/(role+'-deploy-buffer.json')
    if not path.exists():subprocess.run([str(CLI/'solana-keygen'),'new','--no-bip39-passphrase','--silent','-o',str(path)],stdout=subprocess.DEVNULL,check=True)
    os.chmod(path,0o600);buf=pub(path);ba=account(buf)['value'];sigs=[]
    if ba is None:
        size=len(elf)+37;rent=rpc(URL,'getMinimumBalanceForRentExemption',[size]);bh=rpc(URL,'getLatestBlockhash',[{'commitment':'confirmed'}])['value']['blockhash']
        create=(0).to_bytes(4,'little')+rent.to_bytes(8,'little')+size.to_bytes(8,'little')+base58(LOADER)
        e=submit(role+'-buffer-create',[ix(SYSTEM,[[C['payer'],True,True],[buf,True,True]],create),ix(LOADER,[[buf,False,True],[C['payer'],False,False]],bytes(4))],['keys/payer.json',str(path)],bh);wait([e]);sigs.append(e);ba=account(buf)['value']
    assert ba['owner']==LOADER and not ba['executable']
    body=base64.b64decode(ba['data'][0])[37:];assert len(body)==len(elf)
    pending=[i for i in range(0,len(elf),900) if body[i:i+900]!=elf[i:i+900]];write(role+'-plan',{'buffer':buf,'missing_chunks':len(pending),'sha256':spec['sha256']})
    for first in range(0,len(pending),60):
        bh=rpc(URL,'getLatestBlockhash',[{'commitment':'confirmed'}])['value']['blockhash'];batch=[]
        for offset in pending[first:first+60]:
            chunk=elf[offset:offset+900];data=(1).to_bytes(4,'little')+offset.to_bytes(4,'little')+len(chunk).to_bytes(8,'little')+chunk
            e=submit(f'{role}-write-{offset}',[ix(LOADER,[[buf,False,True],[C['payer'],True,False]],data)],['keys/payer.json'],bh);e['offset']=offset;sigs.append(e);batch.append(e);write(role+'-signatures',sigs);time.sleep(.2)
        wait(batch);write(role+'-signatures',sigs);print(f'{role}: {first+len(batch)}/{len(pending)} repaired',flush=True)
    body=base64.b64decode(account(buf)['value']['data'][0])[37:];assert body==elf;write(role+'-buffer-verified',{'sha256':hashlib.sha256(body).hexdigest(),'bytes':len(body),'slot':account(buf)['context']['slot']})
    cmd=[str(CLI/'solana'),'--url',URL,'--keypair','keys/payer.json','--commitment','finalized','--output','json','program','deploy',spec['path'],'--program-id',f'keys/{role}.json','--buffer',str(path),'--max-len',str(len(elf)),'--use-rpc','--max-sign-attempts','2'];write(role+'-deploy-command',cmd)
    with open(O/(role+'-deploy.json'),'w') as stdout,open(O/(role+'-deploy-stderr.txt'),'w') as stderr:status=subprocess.run(cmd,stdout=stdout,stderr=stderr).returncode
    if status:raise RuntimeError(f'{role} deploy CLI exit {status}')
    pa=account(program);assert pa['value']['owner']==LOADER and pa['value']['executable'];raw=base64.b64decode(pa['value']['data'][0]);assert int.from_bytes(raw[:4],'little')==2
    # Programdata address encoded in the linked Program account; use the CLI public account output for its base58 form.
    show=subprocess.check_output([str(CLI/'solana'),'--url',URL,'--output','json','program','show',program],text=True);show=json.loads(show);write(role+'-program',show)
    pd=show['programdataAddress'];pda=account(pd);payload=base64.b64decode(pda['value']['data'][0])[45:];assert payload==elf
    write(role+'-programdata',{'address':pd,'lamports':pda['value']['lamports'],'bytes':len(payload)+45,'elf_sha256':hashlib.sha256(payload).hexdigest(),'context_slot':pda['context']['slot']})
    if role in ('verifier','registry'):
        # V2 certifies exactly an immutable loader deployment; required by this release.
        final=[str(CLI/'solana'),'--url',URL,'--keypair','keys/payer.json','--commitment','finalized','--output','json','program','set-upgrade-authority',program,'--final']
        with open(O/(role+'-immutable.json'),'w') as stdout,open(O/(role+'-immutable-stderr.txt'),'w') as stderr:subprocess.run(final,stdout=stdout,stderr=stderr,check=True)
        finaldata=base64.b64decode(account(pd)['value']['data'][0]);assert finaldata[12]==0 and finaldata[45:]==elf
    write(role+'-complete',{'program':program,'buffer':buf,'wall_seconds':time.monotonic()-started,'key_retained':True});print(role+' deployment verified',flush=True)
