#!/usr/bin/env python3
"""Check real proof-account lifecycle before revoking verifier authority.

The small payload is deliberately not a proof; this measures only lifecycle
plumbing, never verifier correctness or a positive settlement.
"""
import base64,json,struct
import devnet as d
marker=d.EVIDENCE/'lifecycle-preflight-passed.json'
if marker.exists():print(marker.read_text());raise SystemExit(0)
assert d.rpc('getGenesisHash',[])==d.GENESIS
payload=b'ASPIS-LIFECYCLE-PREFLIGHT-ONLY'
name='bad_proof';key=d.IDS[name]
d.upload(name,payload,'lifecycle-preflight-')
# A sealed account rejects writes even from its former upload authority.
rejected=d.transaction('lifecycle-preflight-sealed-write',[d.ix(d.IDS['verifier'],[d.meta(key,False,True),d.meta(d.IDS['authority'],True)],b'\x01'+struct.pack('<II',0,1)+b'x')],submit=False,expect_error=True)
account=d.rpc('getAccountInfo',[key,{'encoding':'base64','commitment':'finalized'}])['value']
assert base64.b64decode(account['data'][0])==b'ASPU'+struct.pack('<I',len(payload))+bytes(32)+payload
rent=account['lamports']
closed=d.transaction('lifecycle-preflight-close',[d.ix(d.IDS['verifier'],[d.meta(key,True,True),d.meta(d.IDS['payer'],False,True)],b'\x40')])
assert d.rpc('getAccountInfo',[key,{'encoding':'base64','commitment':'finalized'}])['value'] is None
assert closed['meta']['postBalances'][0]-closed['meta']['preBalances'][0]==rent-closed['meta']['fee']
v={'real_init_upload_seal_close':True,'payload_is_not_a_proof':True,'sealed_write_rejected':rejected['value']['err'],'refund_lamports':rent,'all_keys_retained':True,'close_signature':closed['transaction']['signatures'][0]};d.save(marker,v);print(json.dumps(v))
