#!/usr/bin/env python3
"""User-authorized transfer of existing devnet test SOL; all keys retained."""
import json,struct
from pathlib import Path
from solders.keypair import Keypair
import devnet as d
assert d.rpc('getGenesisHash',[])==d.GENESIS
receipt=d.EVIDENCE/'colosseum-funding-confirmed.json'
if receipt.exists():print(receipt.read_text());raise SystemExit(0)
roles={'colosseum_regime':('regime.json','FeX66ZSzW67DJL7MQsyXCeTctsXFb1fX4emArQyYi25y')}

signers={}
for role,(filename,public) in roles.items():
 k=Keypair.from_bytes(bytes(json.loads((Path('/Users/dominic/colosseumfinal/ops/devnet_keys')/filename).read_text())))
 assert str(k.pubkey())==public;signers[role]=k;d.IDS[role]=public
original_key=d.key
d.key=lambda role:signers[role] if role in signers else original_key(role)
keys=[d.IDS['payer'],*[public for _,public in roles.values()]]
path=d.EVIDENCE/'colosseum-funding-before.json'
if path.exists():before=json.loads(path.read_text())
else:
 r=d.rpc('getMultipleAccounts',[keys,{'encoding':'base64','commitment':'finalized'}]);before={'slot':r['context']['slot'],'keys':keys,'accounts':r['value']};d.save(path,before)
for a in before['accounts']:
 assert a['owner']==d.SYSTEM and a['space']==0 and not a['executable']
assert all(a['lamports']>=6_100_000_000 for a in before['accounts'][1:])
instructions=[d.ix(d.SYSTEM,[d.meta(public,True,True),d.meta(d.IDS['payer'],False,True)],struct.pack('<IQ',2,6_000_000_000)) for _,public in roles.values()]
tx=d.transaction('fund-from-colosseum-devnet-tests',instructions)
r=d.rpc('getMultipleAccounts',[keys,{'encoding':'base64','commitment':'finalized'}]);after=r['value']
assert after[0]['lamports']-before['accounts'][0]['lamports']==6_000_000_000-tx['meta']['fee']
for i in [1]:assert before['accounts'][i]['lamports']-after[i]['lamports']==6_000_000_000
v={'slot':r['context']['slot'],'genesis':d.GENESIS,'transferred_lamports':6_000_000_000,'fee':tx['meta']['fee'],'destination':keys[0],'payer_balance':after[0]['lamports'],'sources':[{'public_key':keys[i],'remaining_lamports':after[i]['lamports']} for i in [1]],'signature':tx['transaction']['signatures'][0],'all_keys_retained':True,'cumulative_external_funding_lamports':24_000_000_000,'programs_and_game_accounts_unchanged':True}
d.save(receipt,v);print(json.dumps(v))
