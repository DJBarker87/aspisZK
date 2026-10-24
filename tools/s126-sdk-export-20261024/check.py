#!/usr/bin/env python3
"""Source-only release audit; --released additionally hashes the immutable payload."""
from pathlib import Path
import json,hashlib,re,subprocess,sys,stat
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'sdk-current-export-20261024';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((P/'release.json').read_text());m=json.loads((P/'release-manifest.json').read_text());assert sha(P/'release-manifest.json')==r['manifest_sha256']
assert m['unresolved']==[] and m['missing_seeds']==[] and m['nonidentical_current_duplicates']==0 and m['duplicate_count']==42 and m['constant_count']==27287
assert len(m['proof_refresh'])==4 and all(x['same_type'] and x['old_theorem'] and x['new_theorem'] for x in m['proof_refresh'])
assert m['raw_unsafe_or_partial']==['AspisR1.S2W_D189Wrappers.reserve._unsafe_rec']
assert m['status']=='released-proof-refresh-overlay' and '9acc015544' in m['primary_source_revision']
req=json.loads((P/'request.json').read_text());assert req['current_revision']==m['primary_source_revision']
for n,entry in req['targets'].items():
 p=R/entry['source']['path'];assert sha(p)==entry['source']['sha256']
 assert hashlib.sha256(subprocess.check_output(['git','show',req['current_revision']+':'+entry['source']['path']],cwd=R)).hexdigest()==entry['source']['sha256']
replay=E/'sdk-current-entry-privileges-replay-v1';rr=json.loads((replay/'receipt.json').read_text());src=json.loads((P/'privilege-replay-source.json').read_text())
assert rr['exit_status']==0 and rr['swaps']==0 and len(rr['print_axioms'])==4
assert rr['source_sha256']==src['sha256']==sha(replay/'source.lean')==sha(R/src['candidate'])
assert hashlib.sha256(subprocess.check_output(['git','show',src['revision']+':'+src['path']],cwd=R)).hexdigest()==src['sha256']
for a in rr['print_axioms']:
 v=re.findall(r'\[(.*?)\]',a,re.S);assert v and set(v[0].replace(' ','').replace('\n','').split(','))<={'propext','Classical.choice','Quot.sound'}
v2=json.loads((P/'input-pins-v2.json').read_text());assert len(v2['changes'])==1 and v2['changes'][0]['module']=='S2W_EntryPrivileges' and v2['changes'][0]['refreshed_sha256']==rr['object_sha256']
for label,checks in m['post_input_checks'].items():assert checks['all_unchanged'] and checks['sha256']==sha(P/label)
for name,row in m['ledger'].items():
 rec=json.loads((E/name/'receipt.json').read_text());assert all(rec[k]==v for k,v in row.items())
 assert sha(E/name/'source.lean')==rec['source_sha256'] and '-j1' in rec['command'] and '-M4400' in rec['command']
for rel,h in json.loads((P/'tool-pins.json').read_text()).items():assert sha(R/rel)==h
assert not any(p.suffix in ['.olean','.ir','.llbc','.so','.a','.o','.pyc'] for p in P.rglob('*') if p.is_file())
assert not any(p.stat().st_size>5_000_000 for p in P.glob('*.json'))
if '--released' in sys.argv:
 d=Path(r['location']);assert sha(d/'manifest.json')==r['manifest_sha256']
 for f in m['files']:
  p=d/f['relative'];assert p.is_file() and not p.is_symlink() and p.stat().st_size==f['bytes'] and sha(p)==f['sha256']
  assert stat.S_IMODE(p.stat().st_mode)&0o222==0
 assert stat.S_IMODE(d.stat().st_mode)&0o222==0
print(json.dumps(dict(status='PASS',transport_modules=m['transport_modules'],constants=m['constant_count'],unresolved=0,conflicts=0,proof_only_refresh=True,raw_unsafe_compiler_auxiliary=1,released_payload_hashed='--released' in sys.argv,scope=m['scope'])))
