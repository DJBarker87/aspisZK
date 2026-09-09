#!/usr/bin/env python3
"""Refund only the two superseded, empty synthetic SPL token source accounts."""
import base64,json
import devnet as d
assert d.rpc('getGenesisHash',[])==d.GENESIS
configs=[json.loads((d.HERE/n).read_text())['programs_and_accounts'] for n in ['first-setup-identities.json','pre-checkpoint-fix-identities.json']]
addresses=[c['source'] for c in configs]
assert len(set(addresses))==2 and d.IDS['source'] not in addresses
keys=addresses+[d.IDS['payer']]
r=d.rpc('getMultipleAccounts',[keys,{'encoding':'base64','commitment':'finalized'}]);before=r['value']
if all(a is None for a in before[:2]):
    assert (d.EVIDENCE/'empty-source-rent-recovered.json').exists(), 'Resolve recorded refund transaction before retrying.'
    print('Previously recovered; keys retained.');raise SystemExit(0)
for c,a in zip(configs,before[:2]):
    assert c['source_authority']==d.IDS['source_authority']
    assert a and a['owner']==d.TOKEN and not a['executable']
    b=base64.b64decode(a['data'][0])
    assert len(b)==165 and b[:32]==d.pb(c['mint']) and b[32:64]==d.pb(d.IDS['source_authority'])
    assert int.from_bytes(b[64:72],'little')==0 and b[108]==1
    assert b[109:113]==bytes(4) and b[129:133]==bytes(4) # no wrapped SOL or alternate close authority
reclaimed=sum(a['lamports'] for a in before[:2])
d.save(d.EVIDENCE/'empty-source-refund-before.json',{'slot':r['context']['slot'],'keys':keys,'accounts':before})
instructions=[d.ix(d.TOKEN,[d.meta(a,False,True),d.meta(d.IDS['payer'],False,True),d.meta(d.IDS['source_authority'],True)],bytes([9])) for a in addresses]
tx=d.transaction('reclaim-superseded-empty-token-sources',instructions)
r=d.rpc('getMultipleAccounts',[keys,{'encoding':'base64','commitment':'finalized'}]);after=r['value']
assert after[0] is None and after[1] is None
assert after[2]['lamports']-before[2]['lamports']==reclaimed-tx['meta']['fee']
result={'slot':r['context']['slot'],'closed_accounts':addresses,'recipient':d.IDS['payer'],'gross_refund_lamports':reclaimed,'fee_lamports':tx['meta']['fee'],'net_refund_lamports':reclaimed-tx['meta']['fee'],'payer_balance_lamports':after[2]['lamports'],'all_keys_retained':True,'signature':tx['transaction']['signatures'][0]}
d.save(d.EVIDENCE/'empty-source-rent-recovered.json',result);print(json.dumps(result))
