#!/usr/bin/env python3
"""Paced native-loader writes using TxV1; reads and fills only mismatched ranges."""
import base64, hashlib, json, struct, sys, time
from concurrent.futures import ThreadPoolExecutor
import devnet as d
name=sys.argv[1];assert name in ['verifier','pool','registry']
loader='BPFLoaderUpgradeab1e11111111111111111111111'
assert d.rpc('getGenesisHash',[])==d.GENESIS
elf=(d.artifact(name)).read_bytes()
assert hashlib.sha256(elf).hexdigest()==json.loads((d.HERE/'elf-hashes.json').read_text())[name]
buffer=d.IDS[name+'_buffer']
a=d.rpc('getAccountInfo',[buffer,{'encoding':'base64','commitment':'finalized'}])['value']
if a is None:
    d.transaction(name+'-loader-buffer-create',[d.create(name+'_buffer',loader,len(elf)+37),d.ix(loader,[d.meta(buffer,False,True),d.meta(d.IDS['payer'])],struct.pack('<I',0))])
    a=d.rpc('getAccountInfo',[buffer,{'encoding':'base64','commitment':'finalized'}])['value']
assert a['owner']==loader
data=base64.b64decode(a['data'][0]);assert data[:5]==bytes([1,0,0,0,1]) and data[5:37]==d.pb(d.IDS['payer'])
assert len(data)==37+len(elf)
pending=[];sent=0;missing=[]
# Native loader deserialization retains its 1,232-byte per-instruction bound.
# TxV1 can carry three supported 1,200-byte writes in one setup transaction.
for offset in range(0,len(elf),1200):
    chunk=elf[offset:offset+1200]
    if data[37+offset:37+offset+len(chunk)]==chunk:continue
    instruction=d.ix(loader,[d.meta(buffer,False,True),d.meta(d.IDS['payer'],True)],struct.pack('<IIQ',1,offset,len(chunk))+chunk)
    missing.append((offset,instruction))
def submit_batch(batch):
    # Disjoint byte ranges in an initialized buffer; writes are idempotent.
    result=d.transaction(name+'-loader-batch-'+str(batch[0][0]),[i for _,i in batch],wait=False)
    time.sleep(0.35)
    return result
batches=[missing[index:index+3] for index in range(0,len(missing),3)]
with ThreadPoolExecutor(max_workers=2) as workers:
    pending=list(workers.map(submit_batch,batches))
sent=len(pending)
# Reconcile submissions from an interrupted prior uploader as well as this run.
by_signature={item['signature']:item for item in pending if 'signature' in item}
for phase in d.EVIDENCE.glob(name+'-loader-batch-*'):
    for attempt in phase.glob('attempt-*'):
        if (attempt/'submitted.json').exists() and not (attempt/'confirmed.json').exists() and not (attempt/'expired.json').exists():
            signature=json.loads((attempt/'submitted.json').read_text())['signature']
            by_signature[signature]={'signature':signature,'path':str(attempt)}
status_hints={};signatures=list(by_signature)
for start in range(0,len(signatures),128):
    batch=signatures[start:start+128]
    statuses=d.rpc('getSignatureStatuses',[batch,{'searchTransactionHistory':True}])['value']
    status_hints.update(zip(batch,statuses))
def receipt(item):
    if 'signature' in item:return d.confirm(item['signature'],__import__('pathlib').Path(item['path']),status_hints.get(item['signature']))

with ThreadPoolExecutor(max_workers=2) as workers:
    list(workers.map(receipt,by_signature.values()))
a=d.rpc('getAccountInfo',[buffer,{'encoding':'base64','commitment':'finalized'}])['value']
assert base64.b64decode(a['data'][0])[37:]==elf
d.save(d.EVIDENCE/(name+'-loader-buffer-verified.json'),{'buffer':buffer,'sha256':hashlib.sha256(elf).hexdigest(),'bytes':len(elf),'paced_write_transactions':sent,'exact_finalized_bytes':True})
print('Finalized buffer matches exact ELF',flush=True)
