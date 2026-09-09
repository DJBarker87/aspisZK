#!/usr/bin/env python3
"""Revoke ONLY the fresh verifier authority at the required Registry boundary.
The Pool stays upgradeable/closable. This makes verifier rent irreversible.
"""
import base64,hashlib,json,struct
import devnet as d
assert d.rpc('getGenesisHash',[])==d.GENESIS
assert (d.EVIDENCE/'validated-live-setup.json').exists()
assert (d.EVIDENCE/'lifecycle-preflight-passed.json').exists()
setup=json.loads((d.EVIDENCE/'validated-live-setup.json').read_text());assert setup['all_eight_lanes_match_thirteen_deposits'] and setup['canonical_checkpoint_matches_live_roots']
loader='BPFLoaderUpgradeab1e11111111111111111111111'
pd=str(d.Pubkey.find_program_address([d.pb(d.IDS['verifier'])],d.Pubkey.from_string(loader))[0])
a=d.rpc('getAccountInfo',[pd,{'encoding':'base64','commitment':'finalized'}])['value'];b=base64.b64decode(a['data'][0])
assert a['owner']==loader and b[:4]==struct.pack('<I',3) and b[45:]==d.artifact('verifier').read_bytes()
if b[12]==1:
    assert b[13:45]==d.pb(d.IDS['payer'])
    # Native loader SetAuthority with no new authority (pinned interface enum tag 4).
    tx=d.transaction('verifier-required-immutable-certificate',[d.ix(loader,[d.meta(pd,False,True),d.meta(d.IDS['payer'],True)],struct.pack('<I',4))])
else:assert b[12]==0
r=d.rpc('getAccountInfo',[pd,{'encoding':'base64','commitment':'finalized'}]);after=base64.b64decode(r['value']['data'][0]);assert after[12]==0 and after[45:]==b[45:]
d.save(d.EVIDENCE/'verifier-immutable-certificate-ready.json',{'slot':r['context']['slot'],'program':d.IDS['verifier'],'programdata':pd,'authority':None,'elf_sha256':hashlib.sha256(after[45:]).hexdigest(),'reason':'existing selected Registry V2 requires immutable loader deployment','pool_authority_retained':True,'verifier_rent_now_irrecoverable':True})
print('Exact verifier image certified immutable after live setup/lifecycle gates; Pool authority retained.')
