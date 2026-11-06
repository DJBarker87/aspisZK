"""Admit own proposed rows only after final combined, canonical scan and raw ax2 gates."""
from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent
read=lambda p:p.read_text() if p.exists() else lzma.open(str(p)+'.xz').read().decode()
KMX='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
roots=json.load(open(E/'NJE_AUDIT_ROOTS.json'))['roots']
raw=[]
for n in [97,98,99,100]:
 name=f'NJE_L{n:03}';r=json.load(open(E/name/'receipt.json'));assert r['exit_status']==0,name
 admission=json.load(open(E/(name+'-admission.json')));assert admission['exit']==0 and admission['reservation']['allowed'] is True
 assert r['limits']['memory.high']=='6442450944' and r['limits']['memory.max']=='8589934592'
 assert r['limits']['memory.swap.max']=='0' and r['limits']['pids.max']=='64'
 assert str(r['swaps'])=='0'
 if n>=99:raw += [json.loads(l[11:]) for l in read(E/name/'stdout.log').splitlines() if l.startswith('NEP_RESULT ')]
assert sorted(r['root'] for r in raw)==sorted(roots)
assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in raw)
scan=[json.loads(l) for l in read(E/'NJE_LOADED_scan.jsonl').splitlines()]
assert scan and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
closed=json.load(open(E/'NJE_CLOSED.json'));pending=json.load(open(E/'NJE_PENDING.json'))['functions'];allfunctions=[];byrows={}
for entry in closed['functions']+pending:
 key=tuple(entry['rows'])
 if key in byrows:assert byrows[key]==entry,'conflicting duplicate packet '+str(key)
 else:byrows[key]=entry;allfunctions.append(entry)
assert len(allfunctions)==24
assert len({r for f in allfunctions for r in f['rows']})==24
pins=json.load(open(E/'NJE_REUSED_PINS.json'))
for f in allfunctions:
 assert f['complete_carrier'] is True
 assert all(root in roots for root in f['lean_roots'])
 for positive,negative in f['native_pairs']:
  for attempt,expected in [(positive,0),(negative,1)]:
   directory=E if attempt.startswith('NJE_') else E.parent/'multiproof-20261107'
   prefix=attempt.split('_')[0];receipt=directory/attempt/'receipt.json'
   r=json.load(open(receipt));assert r['exit_status']==expected,attempt
   log=read(directory/attempt/'stdout.log')
   assert 'timed out' not in log.lower(),attempt+' timeout gives no credit'
   assert ('VERIFICATION:- SUCCESSFUL' in log or 'VERIFICATION SUCCESSFUL' in log or 'VERIFICATION:- FAILED' in log or 'VERIFICATION FAILED' in log),attempt+' no semantic verdict'
   validation=directory/(attempt+'_validation')
   graph=json.load(open(validation/'NHR_GRAPH_CHECK.json'))
   inactive={('aspis-r1-cert-build','0.0.0',None),('aspis-r1-cert-check','0.0.0',None),('aspis-z4b-probe','0.1.0',None)}
   missing={tuple(x) for x in graph['missing']}
   # Match the pinned canonical stage validator's active frozen closure exactly.
   # The three inactive optional packages are audit entries, not reached edges.
   assert graph['graph_matches_frozen'] and not graph['added'] and not graph['edge_errors'],attempt
   assert not (missing-inactive),attempt+' active dependency missing'
   if missing:assert not any('r1p-check' in p['features'] for p in graph['features']),attempt+' inactive-package condition false'
   lock=json.load(open(validation/(prefix+'_LOCK.json')));assert lock['unchanged'] and lock['before']==lock['after']==graph['lock_before']==graph['lock_after']
   inputs=json.load(open(validation/(prefix+'_INPUTS.json')))
   native=inputs['native_command'];features=native[native.index('--features')+1] if '--features' in native else ''
   assert 'no-entrypoint' not in features,attempt
   assert '--locked' not in native,attempt
   if prefix=='NJE':assert inputs['KMX_patch_sha256']==KMX
   else:
    kmx=validation/(prefix+'_KMX.json')
    if kmx.exists():assert json.load(open(kmx))['patch_sha256']==KMX
   # Every reused stage is pinned by exact receipt/config/validation artifact.
   if prefix=='NJA':
    for p in [receipt,directory/(attempt+'.json')]+[q for q in validation.rglob('*') if q.is_file()]:
     pins[str(p)]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'role':'reused exact native stage'}
packets=json.load(open(E/'NJE_ROW_PACKETS.json'));assert len(packets)==24
for packet in packets:
 assert packet['complete_carrier'] and not packet['aq2_hypothesis_inventory']['extra_logical_hypotheses']
 assert all(c['disposition']=='DISCHARGED' for c in packet['caller_clauses'])
 assert packet['root'] in roots
 packet['admission']='FINAL NJE combined/NFX/raw ax2 gates PASS; candidate CLOSED packet; credit waits for next lead ledger gate'
closed.update(functions=allfunctions,admission='Both own combined gates passed; proposed CLOSED packets only, authoritative NIU unchanged; next lead ledger gate required',target_established=False)
audit=json.load(open(E/'NJE_AUDIT.json'));audit.update(target_established=False,combined_audits_used=2,gate2=dict(combined='NJE_L097',scan='NJE_L098',raw=['NJE_L099','NJE_L100'],all_exit_zero=True,raw_roots=len(raw),modules=len(scan),standard_axioms_only=True,coherence_defects=0),candidate_rows=sorted(p['row'] for p in packets),ledger_credit_pending=True)
for name,x in [('NJE_CLOSED.json',closed),('NJE_ROW_PACKETS.json',packets),('NJE_REUSED_PINS.json',pins),('NJE_RAW_RESULTS_GATE2.json',raw),('NJE_AUDIT.json',audit)]:
 (E/name).write_text(json.dumps(x,indent=2)+'\n')
print('FINAL gate PASS:24 proposed row packets; '+str(len(raw))+' standard-only raw roots; zero coherence defects. Lead ledger credit pending; target not established.')
