"""Collect public local-chain receipts. Uses keygen pubkey only; never reads or hashes secret key bytes."""
import base64,hashlib,json,pathlib,subprocess,sys,time
ROOT=pathlib.Path('/home/dombarker/project-offloads/codex-cx-devnet-rehearse-20261029');E=ROOT/'evidence/devnet-rehearse-20261029'
sys.path.insert(0,str(ROOT))
from r1_devnet_rpc import rpc
from r1_devnet_policy import created_accounts
C=json.load(open(E/'NDZ_local.json'));URL=C['rpc_url'];assert URL=='http://127.0.0.1:18995'
CLI=pathlib.Path(C['cli_dir']);payer=C['payer'];records=[];before=None
while True:
 opts={'commitment':'finalized','limit':1000}
 if before:opts['before']=before
 batch=rpc(URL,'getSignaturesForAddress',[payer,opts])
 records.extend(batch)
 if len(batch)<1000:break
 before=batch[-1]['signature']
rows=[];new=set();metadata={}
cache={}
for directory in ('NDZ_final_deploy','NDZ_final_failure'):
    for path in (E/directory).glob('tx-*.json'):
        tx=json.loads(path.read_text());assert tx is not None;cache[tx['transaction']['signatures'][0]]=tx
for path in (E/'NDZ_final_spend').glob('*-transaction.json'):
    tx=json.loads(path.read_text());cache[tx['transaction']['signatures'][0]]=tx
known={row['signature'] for row in records}
assert known.issubset(cache),'a currently indexed transaction lacks captured metadata'
audit={'currently_indexed_count':len(known),'captured_finalized_count':len(cache),'captured_no_longer_indexed':len(set(cache)-known),'missing_captured_metadata':0,'first_available_block':rpc(URL,'getFirstAvailableBlock',[])}
(E/'NDZ_COLLECTION_AUDIT.json').write_text(json.dumps(audit,indent=2)+'\n')
by_signature={row['signature']:row for row in records}
for sig,tx in cache.items():
    by_signature.setdefault(sig,{'signature':sig,'slot':tx['slot'],'err':tx['meta']['err'],'confirmationStatus':'finalized_from_immediate_receipt'})
records=sorted(by_signature.values(),key=lambda row:(row['slot'],row.get('transactionIndex',0)),reverse=True)
for record in reversed(records):
 sig=record['signature'];tx=cache.get(sig)
 # Reuse finalized transaction receipts to avoid repeating RPC reads.
 for directory in ['NDZ_final_deploy','NDZ_final_spend']:
  path=E/directory/('tx-'+sig+'.json')
  if path.exists():tx=json.loads(path.read_text());break
 if tx is None:tx=rpc(URL,'getTransaction',[sig,{'encoding':'json','commitment':'finalized','maxSupportedTransactionVersion':1}])
 assert tx is not None,(sig,'missing finalized transaction')
 keys=tx['transaction']['message']['accountKeys'];keys=[k if isinstance(k,str) else k['pubkey'] for k in keys]
 pi=keys.index(payer);meta=tx['meta'];new.update(created_accounts(tx))
 row={'signature':sig,'slot':tx['slot'],'err':meta['err'],'fee':meta['fee'],'compute_units':meta.get('computeUnitsConsumed'),'payer_before':meta['preBalances'][pi],'payer_after':meta['postBalances'][pi],'new_accounts':created_accounts(tx),'programs':[keys[i['programIdIndex']] for i in tx['transaction']['message']['instructions']]}
 rows.append(row);metadata[sig]=tx
(E/'NDZ_TRANSACTIONS.json').write_text(json.dumps(rows,indent=2)+'\n')
public_keys=[]
paths=list((E/'keys').glob('*.json'))+list((E/'keys/NDZ_failure_final').glob('*.json'))
for root in (E/'keys').glob(C['key_namespace']+'-*-client64-proof-private'):
 paths.extend(root.glob('attempt-[0-7].json'))
for path in sorted(paths):
 public=subprocess.check_output([str(CLI/'solana-keygen'),'pubkey',str(path)],text=True,stderr=subprocess.DEVNULL).strip()
 public_keys.append({'path':str(path),'public':public,'mode':oct(path.stat().st_mode&0o777)})
(E/'NDZ_LOCAL_KEYS_PUBLIC.json').write_text(json.dumps(public_keys,indent=2)+'\n')
ledger=[]
programdata=json.load(open(E/'NDZ_final_deploy/verifier-programdata.json'))['address']
new.update([C['programs']['verifier'],programdata])
for addr in sorted(new):
 a=rpc(URL,'getAccountInfo',[addr,{'encoding':'base64','commitment':'finalized'}]);v=a['value']
 if v is None:
  ledger.append({'address':addr,'lamports':0,'status':'closed/consumed buffer','recoverable_lamports':0,'locked_lamports':0});continue
 raw=base64.b64decode(v['data'][0]);row={'address':addr,'owner':v['owner'],'lamports':v['lamports'],'data_bytes':len(raw),'slot':a['context']['slot'],'recoverable_lamports':0,'locked_lamports':v['lamports'],'recovery':'no demonstrated close instruction; budget as locked'}
 if addr in [C['programs']['verifier'],programdata]:row['recovery']='permanently locked by verifier finalization'
 if v['owner']=='TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA' and len(raw)==165:
  mintsetup=json.load(open(E/'NDZ_final_spend/mint-setup.json'))
  if addr in [mintsetup['source'],mintsetup['destination']]:
   row.update(recoverable_lamports=v['lamports'],locked_lamports=0,recovery='SPL Token CloseAccount after balance zero; retained NDZ-spend-governance.json signs; recipient '+payer,token_balance=int.from_bytes(raw[64:72],'little'))
 row['devnet_rent_quote']=rpc('https://api.devnet.solana.com','getMinimumBalanceForRentExemption',[len(raw),{'commitment':'finalized'}])
 ledger.append(row)
(E/'NDZ_RENT_LEDGER.json').write_text(json.dumps(ledger,indent=2)+'\n')
# Retain every signed transaction's public metadata in a compact evidence bundle.
import gzip
with gzip.open(E/'NDZ_METADATA.json.gz','wt') as stream:json.dump(metadata,stream,separators=(',',':'))
buffers=json.loads(subprocess.check_output([str(CLI/'solana'),'--keypair',str(E/'keys/payer.json'),'--url',URL,'--output','json','program','show','--buffers','--buffer-authority',payer]))
assert buffers=={'buffers':[]}
(E/'NDZ_FINAL_BUFFERS.json').write_text(json.dumps(buffers,indent=2)+'\n')
assert all(row['compute_units'] is not None for row in rows)
assert 18353204080-rpc(URL,'getBalance',[payer,{'commitment':'finalized'}])['value']==sum(row['fee'] for row in rows)+sum(row['lamports'] for row in ledger)
summary={'transactions':len(rows),'fees_lamports':sum(x['fee'] for x in rows),'compute_units':sum(x['compute_units'] or 0 for x in rows),'initial_lamports':18353204080,'final_balance':rpc(URL,'getBalance',[payer,{'commitment':'finalized'}]),'peak_payer_outlay_lamports':18353204080-min(x['payer_after'] for x in rows),'locked_lamports':sum(x['locked_lamports'] for x in ledger),'recoverable_lamports':sum(x['recoverable_lamports'] for x in ledger),'final_buffers':buffers,'public_write_count':0}
(E/'NDZ_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
