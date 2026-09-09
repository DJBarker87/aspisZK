#!/usr/bin/env python3
"""Derive public metrics from finalized receipts; no RPC or private key access."""
import base64, collections, hashlib, json, pathlib
HERE=pathlib.Path(__file__).resolve().parent
E=HERE/'evidence/live'
def read(p): return json.loads(p.read_text())
assertions=read(E/'settlement-assertions.json')
assert assertions['genuine_positive_transfer']
groups=collections.defaultdict(list)
seen=set()
for p in sorted(E.glob('*/attempt-*/confirmed.json')):
    r=read(p);sig=r['signature']
    if sig in seen:continue
    seen.add(sig);name=p.parent.parent.name
    if name=='atomic-transfer':group='atomic_settlement'
    elif name.startswith('genuine-'):group='genuine_proof_lifecycle'
    elif name.startswith('noncanonical-'):group='malformed_control_lifecycle'
    elif name.startswith(('recipient_zero-','change_zero-')):group='zero_output_control_lifecycle'
    elif name.startswith('lifecycle-preflight-'):group='lifecycle_preflight'
    elif '-loader-' in name:group='program_upload'
    elif name.startswith('fund-from-'):group='funding'
    elif name.startswith('reclaim-'):group='prior_rent_recovery'
    else:group='pool_registry_setup'
    groups[group].append({'phase':name,**r})
before=read(E/'before-settlement.json');after=read(E/'after-settlement.json')
plan=read(HERE/'plan.json');ids=read(HERE/'identities.json')['programs_and_accounts']
def account_info(a):
    if a is None:return None
    b=base64.b64decode(a['data'][0])
    return {'owner':a['owner'],'lamports':a['lamports'],'bytes':len(b),'data_sha256':hashlib.sha256(b).hexdigest()}
transitions={k:{'before':account_info(a),'after':account_info(after['accounts'][k]),'unchanged':a==after['accounts'][k]} for k,a in before['accounts'].items()}
lane=plan['lanes'][plan['output_lane']]
# Layout: lane header 80 bytes; tree sequence [8:16], canonical root [16:48].
def lane_state(s):
    b=base64.b64decode(s['accounts'][lane]['data'][0]);assert len(b)==768
    return {'sequence':int.from_bytes(b[88:96],'little'),'canonical_root_hex':b[96:128].hex()}
prover=[json.loads(line[5:]) for line in (HERE/'evidence/live-prover-honest.log').read_text().splitlines() if line.startswith('PERF ')]
summary={'network':'devnet','assertions':assertions,'prover':prover,
    'before_slot':before['slot'],'after_slot':after['slot'],
    'output_lane':{'address':lane,'before':lane_state(before),'after':lane_state(after)},
    'account_transitions':transitions,
    'transaction_groups':{k:{'count':len(v),'fees_lamports':sum(x['fee'] for x in v),'wire_bytes':sum(x['wire_bytes'] for x in v),'transactions':v} for k,v in groups.items()},
    'note':'Loader CLI deployment transactions are listed separately in authenticated-programs-verifier-pool-registry.json and their raw transaction receipts; groups here count TxV1 harness receipts only.',
    'failures':[{'path':str(p.relative_to(HERE)),'error':read(p)['value']['err']} for p in sorted(E.glob('*/attempt-*/simulation.json')) if read(p)['value']['err'] is not None],
    'expired_attempts':[str(p.relative_to(HERE)) for p in sorted(E.glob('*/attempt-*/expired.json'))]}
(E/'live-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:{x:v[x] for x in ['count','fees_lamports','wire_bytes']} for k,v in summary['transaction_groups'].items()},indent=2))
print(json.dumps(summary['output_lane'],indent=2))
