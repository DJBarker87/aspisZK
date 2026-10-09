#!/usr/bin/env python3
"""Authenticate finalized loader links, immutability and exact executable bytes."""
import base64, hashlib, json, sys
from solders.pubkey import Pubkey
import devnet as d
loader=Pubkey.from_string('BPFLoaderUpgradeab1e11111111111111111111111')
assert d.rpc('getGenesisHash',[])==d.GENESIS
results={}
for name in sys.argv[1:] or ['verifier','pool','registry']:
    program=Pubkey.from_string(d.IDS[name])
    programdata=Pubkey.find_program_address([bytes(program)],loader)[0]
    response=d.rpc('getMultipleAccounts',[[str(program),str(programdata),d.IDS[name+'_buffer']],{'encoding':'base64','commitment':'finalized'}])
    a,b,buffer=response['value'];assert a and b
    assert a['owner']==b['owner']==str(loader) and a['executable'] and not b['executable']
    assert base64.b64decode(a['data'][0])==bytes([2,0,0,0])+bytes(programdata)
    data=base64.b64decode(b['data'][0]);assert data[:4]==bytes([3,0,0,0])
    authority=None if data[12]==0 else str(Pubkey.from_bytes(data[13:45]))
    assert authority is None or (name in ['pool','verifier'] and authority==d.IDS['payer']), 'Unexpected deployment authority'
    if name=='registry':assert authority is None
    expected=(d.artifact(name)).read_bytes()
    assert data[45:]==expected
    assert buffer is None or buffer['lamports']==0
    signatures=d.rpc('getSignaturesForAddress',[str(program),{'commitment':'finalized','limit':20}])
    results[name]={'program':str(program),'programdata':str(programdata),'context_slot':response['context']['slot'],
        'deployment_slot':int.from_bytes(data[4:12],'little'),'immutable':authority is None,'upgrade_authority':authority,'elf_bytes':len(expected),'sha256':hashlib.sha256(expected).hexdigest(),
        'program_lamports':a['lamports'],'programdata_lamports':b['lamports'],'buffer_refunded':True,'signatures':signatures,
        'explorer':'https://explorer.solana.com/address/'+str(program)+'?cluster=devnet'}
    for item in signatures:
        if item['err'] is None:
            tx=d.rpc('getTransaction',[item['signature'],{'encoding':'json','commitment':'finalized','maxSupportedTransactionVersion':1}])
            d.save(d.EVIDENCE/(name+'-deployment-tx-'+item['signature']+'.json'),tx)
    print(json.dumps(results[name]),flush=True)
d.save(d.EVIDENCE/('authenticated-programs-'+'-'.join(results)+'.json'),results)
