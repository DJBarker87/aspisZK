#!/usr/bin/env python3
"""Bounded live semantic-prefix controls; later PCS suffix is unconstructed.
Actual Pool/verifier accounts and same proof identity; never claim accepting PCS.
"""
import json
import devnet as d
assert d.rpc('getGenesisHash',[])==d.GENESIS
for case in ['recipient_zero','change_zero']:
    marker=d.EVIDENCE/(case+'-control-complete.json')
    if marker.exists():continue
    source=d.PRIVATE/case
    candidate=(source/'candidate.bin').read_bytes();body=(source/'proof-1.bin').read_bytes()
    assert len(candidate)==688 and 0<len(body)<=40282
    prefix=case+'-'
    closed_receipts=list((d.EVIDENCE/(prefix+'refund')).glob('attempt-*/confirmed.json'))
    if closed_receipts:
        before=json.loads((d.EVIDENCE/(prefix+'before.json')).read_text())
    else:
        d.upload('proof',candidate+body,prefix)
        before=d.snapshot(prefix+'before')
    terminal=json.loads((source/'terminal.json').read_text())
    if closed_receipts:
        path=sorted((d.EVIDENCE/(prefix+'control')).glob('attempt-*/simulation.json'))[-1]
        rejection=json.loads(path.read_text())['value']
    else:rejection=d.transaction(prefix+'control',[terminal],submit=False,expect_error=True)['value']
    assert rejection['err']=={'InstructionError':[0,{'Custom':4}]},rejection['err']
    assert any(d.IDS['verifier']+' invoke' in x for x in rejection['logs'])
    assert rejection['preBalances'][1:]==rejection['postBalances'][1:]
    assert rejection['preBalances'][0]-rejection['postBalances'][0]==rejection['fee']
    after=json.loads((d.EVIDENCE/(prefix+'after.json')).read_text()) if closed_receipts else d.snapshot(prefix+'after')
    assert before['accounts']==after['accounts']
    rent=before['accounts'][d.IDS['proof']]['lamports']
    closed=d.transaction(prefix+'refund',[d.ix(d.IDS['verifier'],[d.meta(d.IDS['proof'],True,True),d.meta(d.IDS['payer'],False,True)],b'\x40')])
    assert closed['meta']['postBalances'][0]-closed['meta']['preBalances'][0]==rent-closed['meta']['fee']
    assert d.rpc('getAccountInfo',[d.IDS['proof'],{'encoding':'base64','commitment':'finalized'}])['value'] is None
    d.save(marker,{'case':case,'real_C1_C2_commitments':True,'semantic_rounds':10,'PCS_suffix_unconstructed':True,'complete_accepting_proof_claimed':False,'fixed_seed':1,'grinding_attempts':0,'verifier_invoked':True,'error':rejection['err'],'units':rejection['unitsConsumed'],'settlement_unchanged':True,'refund_lamports':rent,'keys_retained':True})
    print(case+' rejected by live semantic verifier; settlement unchanged; proof rent refunded.',flush=True)
