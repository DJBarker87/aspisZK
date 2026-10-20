#!/usr/bin/env python3
"""Collect finalized transaction metadata without embedding ELF upload bytes."""
import json,pathlib,subprocess,sys,time
from r1_devnet_rpc import rpc
C=json.load(open(sys.argv[1]));root=pathlib.Path(sys.argv[2]);out=pathlib.Path(sys.argv[3]);out.mkdir(exist_ok=True)
known={}
p=out/'transactions.json'
if p.exists():known=json.load(open(p))
addresses=set(C['programs'].values())
if C.get('carrier'):addresses.add(C['carrier'])
cli=pathlib.Path.home()/'.local/share/solana/install/active_release/bin/solana-keygen'
for key in pathlib.Path('keys').glob('*deploy-buffer.json'):
    addresses.add(subprocess.check_output([str(cli),'pubkey',str(key)],text=True).strip())
candidates={}
for address in sorted(addresses):
    before=None;history=[]
    while True:
        opts={'limit':1000,'commitment':'finalized'}
        if before:opts['before']=before
        values=rpc(C['rpc_url'],'getSignaturesForAddress',[address,opts]);history+=values
        for x in values:candidates[x['signature']]=x
        if len(values)<1000:break
        before=values[-1]['signature'];time.sleep(.3)
    (out/(address+'-history.json')).write_text(json.dumps(history,indent=2))
def scan(v):
    if isinstance(v,dict):
        sig=v.get('signature')
        if isinstance(sig,str) and 80<=len(sig)<=90:candidates.setdefault(sig,{})
        for x in v.values():scan(x)
    elif isinstance(v,list):
        for x in v:scan(x)
for path in root.rglob('*.json'):
    if out==path.parent or '-private' in str(path) or '-transaction.json' in path.name:continue
    try:scan(json.load(open(path)))
    except (ValueError,OSError):pass
for i,sig in enumerate(sorted(candidates)):
    if sig in known:continue
    tx=rpc(C['rpc_url'],'getTransaction',[sig,{'encoding':'json','commitment':'finalized','maxSupportedTransactionVersion':1}])
    if tx is None:continue
    m=tx['meta'];known[sig]={'signature':sig,'explorer':f'https://explorer.solana.com/tx/{sig}?cluster=devnet','slot':tx['slot'],'block_time':tx.get('blockTime'),'compute_units':m.get('computeUnitsConsumed'),'fee':m['fee'],'error':m['err'],'logs':m.get('logMessages'),'finalized':True}
    if len(known)%20==0:p.write_text(json.dumps(known,indent=2));print(f'{len(known)} metadata records',flush=True)
    time.sleep(.25)
p.write_text(json.dumps(known,indent=2));(out/'summary.json').write_text(json.dumps({'candidate_signatures':len(candidates),'finalized_metadata':len(known),'missing':sorted(set(candidates)-set(known))},indent=2))
