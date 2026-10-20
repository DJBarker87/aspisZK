#!/usr/bin/env python3
"""Resume only mismatched loader bytes using paced TxV1 RPC writes."""
import base64,hashlib,json,pathlib,subprocess,sys,time
from r1_devnet_rpc import rpc
c=json.load(open(sys.argv[1]));out=pathlib.Path(sys.argv[2]);out.mkdir(exist_ok=False,mode=0o700)
url=c['rpc_url'];loader='BPFLoaderUpgradeab1e11111111111111111111111'
cli=pathlib.Path.home()/'.local/share/solana/install/active_release/bin'
buffer=subprocess.check_output([str(cli/'solana-keygen'),'pubkey','keys/verifier-deploy-buffer.json'],text=True).strip()
elf=pathlib.Path(c['artifacts']['verifier']).read_bytes();assert hashlib.sha256(elf).hexdigest()==c['release_artifacts']['devnet_verifier']['sha256']
def body():return base64.b64decode(rpc(url,'getAccountInfo',[buffer,{'encoding':'base64','commitment':'finalized'}])['value']['data'][0])[37:]
initial=body();pending=[i for i in range(0,len(elf),900) if initial[i:i+900]!=elf[i:i+900]]
(out/'plan.json').write_text(json.dumps({'buffer':buffer,'mismatched_chunks':len(pending),'chunk_bytes':900,'artifact_sha256':hashlib.sha256(elf).hexdigest()},indent=2))
all_sigs=[]
for start in range(0,len(pending),30):
    offsets=pending[start:start+30];bh=rpc(url,'getLatestBlockhash',[{'commitment':'confirmed'}])['value'];batch=[]
    for offset in offsets:
        chunk=elf[offset:offset+900];data=(1).to_bytes(4,'little')+offset.to_bytes(4,'little')+len(chunk).to_bytes(8,'little')+chunk
        q={'keys':['keys/payer.json'],'blockhash':bh['blockhash'],'instructions':[{'program':loader,'accounts':[[buffer,False,True],[c['payer'],True,False]],'data':data.hex()}]}
        signed=json.loads(subprocess.check_output(['native-target/release/devnet_spend'],input=json.dumps(q).encode()))
        wire=base64.b64encode(bytes.fromhex(signed['hex'])).decode()
        sim=rpc(url,'simulateTransaction',[wire,{'encoding':'base64','sigVerify':True,'commitment':'confirmed'}])
        (out/f'simulation-{offset}.json').write_text(json.dumps(sim))
        if sim['value']['err']:raise RuntimeError(sim)
        sig=rpc(url,'sendTransaction',[wire,{'encoding':'base64','skipPreflight':False,'maxRetries':5,'preflightCommitment':'confirmed'}]);assert sig==signed['signature']
        entry={'signature':sig,'offset':offset,'bytes':len(chunk),'serialized_bytes':signed['bytes'],'explorer':f'https://explorer.solana.com/tx/{sig}?cluster=devnet'}
        batch.append(entry);all_sigs.append(entry)
        (out/'signatures.json').write_text(json.dumps(all_sigs,indent=2));time.sleep(.4)
    begin=time.monotonic()
    while True:
        statuses=rpc(url,'getSignatureStatuses',[[x['signature'] for x in batch],{'searchTransactionHistory':True}])['value']
        if all(s and s['confirmationStatus']=='finalized' for s in statuses):break
        if time.monotonic()-begin>100:raise RuntimeError('batch not finalized; inspect signatures before resume')
        time.sleep(2)
    for entry,status in zip(batch,statuses):
        entry.update(status)
        if status['err']:raise RuntimeError(status)
    (out/'signatures.json').write_text(json.dumps(all_sigs,indent=2));print(f'finalized {start+len(batch)}/{len(pending)} chunks',flush=True)
final=body();assert final==elf
(out/'verified.json').write_text(json.dumps({'bytes':len(final),'sha256':hashlib.sha256(final).hexdigest(),'all_bytes_equal':True},indent=2))
print('buffer fully verified',flush=True)
