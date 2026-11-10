"""NPN_: facts of NPC_LOCAL_TRANSACTIONS (transfer pair, records 35/36) used by the plan.
Usage: python3 -I NPN_recording_facts.py <decompressed NPC_LOCAL_TRANSACTIONS.json>"""
import json,sys,base64,hashlib
al='123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'
def dec(s):
    n=0
    for c in s: n=n*58+al.index(c)
    return n.to_bytes(32,'big')
def enc(b):
    n=int.from_bytes(bytes(b),'big'); s=''
    while n: n,r=divmod(n,58); s=al[r]+s
    return s
def data(a):
    v=a.get('data_base64')
    if not v: return b''
    return base64.b64decode(v[0] if isinstance(v,list) else v)
raw=open(sys.argv[1],'rb').read(); d=json.loads(raw); T=d['transactions']
t1,t2=T[35],T[36]; out={'source_sha256':hashlib.sha256(raw).hexdigest(),'tx1':t1['name'],'tx2':t2['name']}
m1=t1['transaction_json']['transaction']['message']; k1=m1['accountKeys']
out['tx1_accounts']=[k1[a] for a in m1['instructions'][0]['accounts']]
m2=t2['transaction_json']['transaction']['message']; k2=m2['accountKeys']
inner=[ [k2[a] for a in i['accounts']] for g in t2['transaction_json']['meta']['innerInstructions'] for i in g['instructions'] if k2[i['programIdIndex']].startswith('CSnhz')]
out['tx2_verifier_cpi_accounts']=inner
out['tx1_account2_eq_tx2_cpi_account6']=out['tx1_accounts'][2]==inner[0][6]
post1={a['key']:a for a in t1['post']['accounts']}; pre2={a['key']:a for a in t2['pre']['accounts']}
out['shared_post1_eq_pre2']={k[:12]:(data(post1[k])==data(pre2[k]) and post1[k]['lamports']==pre2[k]['lamports']) for k in post1 if k in pre2}
out['slots']={'tx1':t1['tx_slot'],'tx2':t2['tx_slot'],'tx1_isolation':t1['isolation'],'tx2_isolation':t2['isolation']}
out['cu']={'tx1':t1['transaction_json']['meta']['computeUnitsConsumed'],'tx2':t2['transaction_json']['meta']['computeUnitsConsumed']}
ck=[a for a in t1['pre']['accounts'] if a['key']==out['tx1_accounts'][2]][0]
out['checkpoint_owner']=ck['owner']
model={'CPH_Program.verifier':enc([95,12,126,84,84,184,191,44,127,237,85,250,26,65,11,162,234,180,193,149,162,190,100,247,226,253,59,0,225,151,154,141]),
 'LIB_Deployed.deployed.pool (ids false)':enc([65]*32),'LIB_Deployed.deployed.registry (ids false)':enc([68]*32),
 'LIB_Deployed.devnet.pool':enc([160,19,98,42,240,202,109,154,218,233,162,167,169,176,187,66,122,69,190,75,195,45,233,50,40,58,26,66,26,133,145,52]),
 'LIB_Deployed.devnet.registry':enc([131,9,163,201,153,45,35,222,189,104,139,224,185,96,72,135,226,88,106,68,10,156,60,72,82,28,53,49,227,146,232,171])}
out['model_ids']=model
ids={'verifier':'CSnhzGdHQuzMW512CSunJzHrutcmh8ZAFzqx2z1zKorQ','pool':'BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs','registry':'9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q'}
occ=[]
for t in (t1,t2):
    for a in t['pre']['accounts']:
        b=data(a)
        for n,k in ids.items():
            if dec(k) in b: occ.append([t['name'],'account '+a['key'],len(b),n,b.find(dec(k))])
    for ins in t['instructions']:
        b=bytes.fromhex(ins['data_hex'])
        for n,k in ids.items():
            if dec(k) in b: occ.append([t['name'],'ixdata',len(b),n,b.find(dec(k))])
out['recorded_id_occurrences_in_data']=occ
out['proof_statement_checkpoint_embed_ids']=any(o[1].split()[-1] in out['tx1_accounts'] for o in occ)
print(json.dumps(out,indent=1))
