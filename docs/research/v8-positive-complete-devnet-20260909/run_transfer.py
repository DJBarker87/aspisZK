#!/usr/bin/env python3
"""Real proof: malformed control at the SAME proof identity, refund, genuine transfer, replay."""
import base64, hashlib, json, struct
import devnet as d
context=d.PRIVATE/'context'
body=(d.PRIVATE/'proof/proof-1.bin').read_bytes()
candidate=(context/'candidate.bin').read_bytes()
assert len(candidate)==688 and 0<len(body)<=40282
payload=candidate+body
terminal=json.loads((context/'terminal.json').read_text())
def data(a):return base64.b64decode(a['data'][0])
def unchanged(before,after):
    assert before['accounts']==after['accounts']
def rejection_balances(result):
    value=result['value'];pre=value['preBalances'];post=value['postBalances']
    assert len(pre)==len(post)>0 and pre[1:]==post[1:]
    assert pre[0]-post[0]==value['fee']

# Deliberate noncanonical first field element; all identities and lengths remain genuine.
# Close/recreate is an existing authenticated lifecycle, not direct account injection.
if not (d.EVIDENCE/'malformed-control-complete.json').exists():
    bad=bytearray(payload);bad[688:692]=struct.pack('<I',2147483647)
    assert bytes(bad)!=payload
    closed_receipts=list((d.EVIDENCE/'noncanonical-proof-refund').glob('attempt-*/confirmed.json'))
    if closed_receipts:
        before=json.loads((d.EVIDENCE/'before-noncanonical-control.json').read_text())
    else:
        d.upload('proof',bytes(bad),'noncanonical-')
        before=d.snapshot('before-noncanonical-control')
    if closed_receipts:
        attempts=sorted((d.EVIDENCE/'noncanonical-proof-control').glob('attempt-*/simulation.json'))
        rejected=json.loads(attempts[-1].read_text())
    else:
        rejected=d.transaction('noncanonical-proof-control',[terminal],submit=False,expect_error=True)
    rejection_balances(rejected)
    after=json.loads((d.EVIDENCE/'after-noncanonical-control.json').read_text()) if closed_receipts else d.snapshot('after-noncanonical-control')
    unchanged(before,after)
    assert any(d.IDS['verifier']+' invoke' in line for line in rejected['value']['logs'])
    lamports=before['accounts'][d.IDS['proof']]['lamports']
    closed=d.transaction('noncanonical-proof-refund',[d.ix(d.IDS['verifier'],[d.meta(d.IDS['proof'],True,True),d.meta(d.IDS['payer'],False,True)],bytes([64]))])
    refunded=d.snapshot('after-noncanonical-refund')
    assert refunded['accounts'][d.IDS['proof']] is None
    assert refunded['accounts'][d.IDS['payer']]['lamports']-after['accounts'][d.IDS['payer']]['lamports']==lamports-closed['meta']['fee']
    d.save(d.EVIDENCE/'malformed-control-complete.json',{'mutation':'first proof-body M31 limb replaced by modulus 2147483647','same_proof_identity':True,'verifier_invoked':True,'simulation_error':rejected['value']['err'],'settlement_accounts_unchanged':True,'proof_rent_refunded':lamports,'key_retained':True})

# Retain the pre-settlement snapshot across process restarts and receipt reuse.
before_path=d.EVIDENCE/'before-settlement.json'
if before_path.exists():
    before=json.loads(before_path.read_text())
else:
    d.upload('proof',payload,'genuine-')
    before=d.snapshot('before-settlement')
d.assert_token_state(before)
tx=d.transaction('atomic-transfer',[terminal])
after=d.snapshot('after-settlement')
d.assert_token_state(after)
lane=d.PLAN['lanes'][d.PLAN['output_lane']];page=d.PLAN['pages'][d.PLAN['output_lane']];marker=d.PLAN['nullifier_marker']
for address,filename in [(lane,'expected-lane.bin'),(page,'expected-history.bin'),(marker,'expected-marker.bin')]:
    assert after['accounts'][address]['owner']==d.IDS['pool']
    assert data(after['accounts'][address])==(context/filename).read_bytes()
assert before['accounts'][marker] is None
changed={lane,page,marker,d.IDS['payer']}
for address,value in before['accounts'].items():
    if address not in changed:assert value==after['accounts'][address],address
assert before['accounts'][lane]['lamports']==after['accounts'][lane]['lamports']
assert before['accounts'][page]['lamports']==after['accounts'][page]['lamports']
assert before['accounts'][d.IDS['payer']]['lamports']-after['accounts'][d.IDS['payer']]['lamports']==tx['meta']['fee']+after['accounts'][marker]['lamports']
returned=tx['meta']['returnData'];assert returned['programId']==d.IDS['pool']
assert base64.b64decode(returned['data'][0])==(context/'expected-result.bin').read_bytes()
assert data(after['accounts'][d.IDS['proof']])==b'ASPU'+struct.pack('<I',len(payload))+bytes(32)+payload
replay_before=d.snapshot('before-replay-control')
replay=d.transaction('replay-control',[terminal],submit=False,expect_error=True)
rejection_balances(replay)
assert replay['value']['err']=={'InstructionError':[0,{'Custom':0x41532026}]}, 'Expected the real Pool NullifierAlreadyConsumed rejection.'
replay_after=d.snapshot('after-replay-control');unchanged(replay_before,replay_after)
d.save(d.EVIDENCE/'settlement-assertions.json',{'genuine_positive_transfer':True,'input_value':1000,'recipient_value':600,'change_value':400,'proof_body_bytes':len(body),'candidate_overhead_bytes':688,'account_header_bytes':40,'account_bytes':40+len(payload),'body_sha256':hashlib.sha256(body).hexdigest(),'exact_lane_image':True,'exact_history_image':True,'exact_nullifier_image':True,'exact_returned_statement':True,'other_lanes_master_checkpoint_registry_mint_vault_source_unchanged':True,'proof_stays_sealed_and_readonly':True,'nullifier_consumed':True,'payer_delta_is_fee_plus_marker_rent':True,'replay_error':replay['value']['err'],'replay_settlement_accounts_unchanged':True,'negative_controls_are_simulations':True,'declared_cu':d.CU,'confirmed_units':tx['meta']['computeUnitsConsumed'],'fee':tx['meta']['fee']})
print('Confirmed positive transfer and exact settlement assertions passed; malformed and replay simulations rejected.',flush=True)
