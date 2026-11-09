"""NPC_ Phase 1: read-only devnet snapshot. getAccountInfo/getBalance/getSlot only; no signing, no keys."""
import json,sys,base64,hashlib,urllib.request,time
U='https://api.devnet.solana.com'
def rpc(m,p):
    r=urllib.request.Request(U,json.dumps(dict(jsonrpc='2.0',id=1,method=m,params=p)).encode(),{'content-type':'application/json'})
    for i in range(5):
        try: return json.load(urllib.request.urlopen(r,timeout=30))['result']
        except Exception as e: err=e; time.sleep(2)
    raise err
A="123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
def b58e(b):
    n=int.from_bytes(b,'big'); s=''
    while n: n,r=divmod(n,58); s=A[r]+s
    return '1'*(len(b)-len(b.lstrip(b'\0')))+s
def acct(a):
    r=rpc('getAccountInfo',[a,dict(encoding='base64',commitment='finalized')])
    v=r['value']
    if v is None: return dict(address=a,slot=r['context']['slot'],exists=False)
    d=base64.b64decode(v['data'][0])
    return dict(address=a,slot=r['context']['slot'],exists=True,owner=v['owner'],lamports=v['lamports'],executable=v['executable'],data_len=len(d),data_sha256=hashlib.sha256(d).hexdigest(),head_hex=d[:8].hex(),_d=d)
out=dict(kind='NPC_DEVNET_READONLY',rpc=U,genesis=rpc('getGenesisHash',[]),version=rpc('getVersion',[]),finalized_slot=rpc('getSlot',[dict(commitment='finalized')]),accounts={})
names=dict(pool_program='BmsNikL97uF7bb1hMnJxsas7a9LjjK8vvT5Q1b7W34Qs',verifier_program='CSnhzGdHQuzMW512CSunJzHrutcmh8ZAFzqx2z1zKorQ',registry_program='9pWwAcBgwhnkA8JWSA6GvjpYqGzSibLF6GqGH8v6EC9Q',carrier_program='3jEFrv5Npn3RmFMW1Cbzq5yEiLdeFB5vbBGmnfoqK9vN',
 fresh_pool_master='4GQ9Gnmi71ZonpVSJRsmRxyK2UMdVJJCXjYrbTetha1G',fresh_registry='CRqLcv1MfBq73gQ3unk7s7EArnUQqZvUbDdqTX8We2Pu',active_entry='6Hd8P6negaxMLFqY3t1Q34PDwz32D8rD7qxkutP993V1',vault='4kjEXoJ7YdwgZJaome64VX8fyqNNbdVWXbCFB4LT3Eyu',mint='EhZ4nakdh7U1SivMhKjZy5XhYxHMNMXgmfZESa2RU5VM',
 payer='CVZJcAv97von8njTJSyLVQ9X33NAKQYbEXFKnAYvst9t',lost_pool_authority='Xjb7roDVPDSPoZpUmDVUW5SMx21x7oQEg16dhb5TDXD')
for k,a in names.items():
    r=acct(a); d=r.pop('_d',None)
    if d is not None and r['owner']=='BPFLoaderUpgradeab1e11111111111111111111111' and d[:4]==b'\x02\0\0\0':
        pd=b58e(d[4:36]); p=acct(pd); pdd=p.pop('_d')
        p['upgrade_authority']=b58e(pdd[13:45]) if pdd[12]==1 else None
        p['last_deploy_slot']=int.from_bytes(pdd[4:12],'little')
        elf=pdd[45:]; p['elf_bytes_incl_padding']=len(elf); p['elf_sha256_full_payload']=hashlib.sha256(elf).hexdigest()
        r['programdata']=p
    if k=='vault' and d is not None: r['token_amount']=int.from_bytes(d[64:72],'little')
    out['accounts'][k]=r
out['payer_balance_lamports']=out['accounts']['payer']['lamports']
json.dump(out,open(sys.argv[1],'w'),indent=1); print(json.dumps({k:(v.get('programdata',{}).get('upgrade_authority','-'),v.get('lamports')) for k,v in out['accounts'].items()},indent=0))
