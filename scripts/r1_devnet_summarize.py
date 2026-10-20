#!/usr/bin/env python3
"""Summarize exported public receipts. Does not access RPC or keys."""
import json,pathlib,subprocess,sys
root=pathlib.Path(sys.argv[1]);receipts=root/'receipts'
def read(path,default=None):
    try:return json.load(open(path))
    except (OSError,ValueError):return default
old=read(root/'signatures.json',{})
external=[v for v in old.get('transactions',[]) if v.get('submitted_by_worker') is False]
transactions={}
def add(v,phase,receipt):
    sig=v.get('signature')
    if not isinstance(sig,str):return
    entry=transactions.setdefault(sig,{'phase':phase,'submitted_by_worker':True,'signature':sig,'explorer_url':f'https://explorer.solana.com/tx/{sig}?cluster=devnet','receipts':[]})
    if receipt not in entry['receipts']:entry['receipts'].append(receipt)
    for target,names in {'slot':['slot'],'block_time':['block_time','blockTime'],'err':['error','err'],'compute_units_consumed':['compute_units'],'fee_lamports':['fee'],'submission_confirmation_wall_seconds':['wall_seconds']}.items():
        for key in names:
            if key in v and (v[key] is not None or target not in entry):entry[target]=v[key];break
    if v.get('finalized') or v.get('confirmationStatus')=='finalized':entry['confirmation_status']='finalized'
    if phase not in ['program_history','loader_buffer_history','metadata']:entry['phase']=phase
# Final history inventories establish landed signatures and slots, including
# original CLI writes whose unpublished/expired attempts were not exposed.
for path in receipts.glob('histories/*-history.json'):
    for v in read(path,[]):add(v,'loader_buffer_history',str(path.relative_to(root)))
for folder in ['metadata','spend-metadata']:
    for sig,v in read(receipts/folder/'transactions.json',{}).items():add(v,'metadata',str((receipts/folder/'transactions.json').relative_to(root)))
for path in (receipts/'spend').glob('*.json'):
    v=read(path,{})
    if isinstance(v,dict) and v.get('finalized') and v.get('signature'):add(v,path.stem,str(path.relative_to(root)))
for folder in receipts.glob('deploy-*'):
    for path in folder.glob('*-deploy.json'):
        v=read(path,{})
        if isinstance(v,dict) and v.get('signature'):add(v,'deploy-'+path.name.removesuffix('-deploy.json'),str(path.relative_to(root)))
# Preserve signatures recorded before submission even if they never landed.
for folder in receipts.glob('deploy-*'):
    for path in folder.glob('*-attempt-*.json'):
        if any(x in path.name for x in ['simulation','error']):continue
        v=read(path,{})
        if isinstance(v,dict) and v.get('signature'):
            sig=v['signature']
            if sig not in transactions:add(v,'deployment-signed-attempt',str(path.relative_to(root)))
for v in transactions.values():
    v.setdefault('compute_units_consumed',None);v.setdefault('confirmation_status','recorded_attempt_not_in_finalized_history')
phases={}
for op in ['transfer','withdrawal']:
    proof=read(receipts/'spend'/f'{op}-proof-plan.json',{})
    phase={'prove':{'wall_seconds':proof.get('prove_wall_seconds'),'p_r1':proof.get('p_r1'),'attempts':proof.get('attempts'),'compute_units':None}}
    phase['uploads']=read(receipts/'spend'/f'{op}-uploads-phase.json',{})
    for short,long in [('tx1','stage1'),('tx2','stage2')]:phase[short]=read(receipts/'spend'/f'{op}-{long}.json',{})
    for check in ['settlement-validation','token-balances','replay-validation','mutation-validation']:phase[check]=read(receipts/'spend'/f'{op}-{check}.json',{})
    phases[op]=phase
complete=read(receipts/'spend'/'complete.json')
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
summary={'schema':'aspis.r1.devnet-signatures.v2','cluster':'devnet','source_revision':revision,'status':'complete' if complete else 'incomplete','transactions':external+sorted(transactions.values(),key=lambda v:(v.get('slot',10**20),v['signature'])),'worker_submitted_transaction_count':sum(v.get('confirmation_status')=='finalized' for v in transactions.values()),'deploy_count':sum(v['phase'].startswith('deploy-') for v in transactions.values()),'upload_count':sum(p.get('uploads',{}).get('proof_count',0)+p.get('uploads',{}).get('statement_count',0) for p in phases.values()),'spend_count':sum(bool(p['tx2'].get('finalized') and p['tx2'].get('error') is None) for p in phases.values()),'phases':phases,'completion':complete,'note':'All spend/setup CU, slots, fees and wall times come from finalized transaction receipts. Loader-buffer histories inventory landed signatures; loader-write CU is sampled where metadata was fetched. Unpublished failed CLI signing attempts are not recoverable from its empty stdout. Keys remain retained on the host.'}
(root/'signatures.json').write_text(json.dumps(summary,indent=2)+'\n')
(root/'phase-summary.json').write_text(json.dumps({'status':summary['status'],'phases':phases},indent=2)+'\n')
print(json.dumps({'status':summary['status'],'landed_worker_signatures':summary['worker_submitted_transaction_count'],'deploy_count':summary['deploy_count'],'upload_count':summary['upload_count'],'spend_count':summary['spend_count']},indent=2))
