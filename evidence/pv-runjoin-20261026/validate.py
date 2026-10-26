#!/usr/bin/env python3
"""Check this job's evidence and unchanged endpoint; no build or mutation."""
import hashlib,json,pathlib,re,subprocess
base=pathlib.Path(__file__).resolve().parent
root=base.parents[1]
lean=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
receipts=[json.loads(p.read_text()) for p in sorted(base.glob('receipt-*.json'))]
allowed={'propext','Classical.choice','Quot.sound'}
for r in receipts:
    source=(base/r['source_snapshot']).read_bytes()
    assert hashlib.sha256(source).hexdigest()==r['source_sha256']
    if r['exit']==['exit=0']:
        assert r['axioms']
        for line in r['axioms']:
            names=set(re.findall(r'\[([\s\S]*?)\]',line)[0].replace('\n','').replace(' ','').split(','))
            assert names<=allowed,(r['attempt'],names)
for p in lean.glob('PV_RunJoin_*.lean'):
    digest=hashlib.sha256(p.read_bytes()).hexdigest()
    assert any(r['source_sha256']==digest and r['exit']==['exit=0'] for r in receipts),p
    assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxHeartbeats|maxRecDepth)\b',p.read_text()),p
original=(lean/'PrivacyR1HeadlineDeployedReal.lean').read_text()
endpoint=(lean/'PV_RunJoin_Endpoint.lean').read_text()
def conclusion(s,n):
    start=s.index(' :\n    (∀ (adv',s.index('theorem '+n)); return s[start:s.index(' := by',start)]
assert conclusion(original,'privacy_headline_deployed')==conclusion(endpoint,'privacy_headline_from_premises')
fields=re.findall(r'^  (\w+_V0\d+) :',endpoint,re.M)
assert fields==['uniform_V037','disclosed_V038','observerOracle_V038']
assert subprocess.check_output(['git','diff','c0f03d8a0c5bcb2f6db6616d99b47630eff972a3','--',str(lean/'PrivacyR1HeadlineDeployedReal.lean')],cwd=root)==b''
print(json.dumps(dict(attempts=len(receipts),passes=sum(r['exit']==['exit=0'] for r in receipts),failures=sum(r['exit']!=['exit=0'] for r in receipts),fields=fields,current_sources_match_successful_snapshots=True,conclusion_byte_equal=True,accepted_axioms_standard=True),indent=2))
