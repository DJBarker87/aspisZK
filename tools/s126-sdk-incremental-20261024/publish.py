#!/usr/bin/env python3
"""Publish incremental UNTRUSTED raw data only after combined closure audit."""
from pathlib import Path
import hashlib,json,shutil
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'sdk-current-incremental-20261024';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
config=json.loads((P/'input-v2.json').read_text());W=Path(config['dest']).parent;dest=Path('/private/tmp/s126-sdk-current-incremental-release-20261024-v1');assert not dest.exists()
export=E/'sdk-current-incremental-export-v2';audit=E/'sdk-current-incremental-audit-v1'
def one(lines,prefix):
 values=[json.loads(line[len(prefix):]) for line in lines if line.startswith(prefix)];assert len(values)==1,(prefix,len(values));return values[0]
exlines=(export/'lean.log').read_text().splitlines();aulines=(audit/'lean.log').read_text().splitlines();summary=one(aulines,'AUDIT_SUMMARY ');exsummary=one(exlines,'SUMMARY ')
assert one(exlines,'UNRESOLVED ')==[] and summary['conflicts']==0 and summary['unresolved']==[] and summary['missing_seeds']==[]
assert exsummary['baseline_constants']==27287 and summary['constants']==27287+exsummary['constants']
base=json.loads((E/'sdk-current-export-20261024/release.json').read_text());basemanifest=json.loads((Path(base['location'])/'manifest.json').read_text());assert sha(Path(base['location'])/'manifest.json')==base['manifest_sha256']
refresh=[json.loads(line[len('PROOF_REFRESH '):]) for line in aulines if line.startswith('PROOF_REFRESH ')]
assert len(refresh)==2 and all(row['same_type'] and row['old_theorem'] and row['new_theorem'] for row in refresh)
unsafe=[json.loads(line[len('UNSAFE_OR_PARTIAL '):]) for line in aulines if line.startswith('UNSAFE_OR_PARTIAL ')];assert sorted(unsafe)==sorted(basemanifest['raw_unsafe_or_partial'])
rows=[json.loads(line[len('CONSTANT '):]) for line in aulines if line.startswith('CONSTANT ')];oldnames=set(config['baseline_names']);newrows=[row for row in rows if row['name'] not in oldnames];assert len(newrows)==exsummary['constants']
(W/'constants-incremental.jsonl').write_text('\n'.join(json.dumps(row,separators=(',',':')) for row in newrows)+'\n')
(W/'edges-incremental.jsonl').write_text('\n'.join(line[len('EDGE '):] for line in exlines if line.startswith('EDGE '))+'\n')
(W/'duplicates-combined.jsonl').write_text('\n'.join(line[len('DUPLICATE '):] for line in aulines if line.startswith('DUPLICATE '))+'\n')
meta=W/'metadata';meta.mkdir();logs=W/'logs';logs.mkdir();ledger={}
for name,path in [('sdk-current-accepted-proof-replay-v1',E/'sdk-current-accepted-proof-replay-v1'),('sdk-current-incremental-export-v2',export),('sdk-current-incremental-audit-v1',audit)]:
 r=json.loads((path/'receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0
 assert '-j1' in r['command'] and '-M4400' in r['command']
 ledger[name]={k:r[k] for k in ['target','exit_status','wall_seconds','peak_rss_bytes','swaps','print_axioms','source_sha256']}
 for f in ['source.lean','command.json','receipt.json','time.log']:shutil.copyfile(path/f,meta/(name+'-'+f))
 shutil.copyfile(path/'lean.log',logs/(name+'.log'))
# Do not silently mutate the current inputs after export.
pins=json.loads((P/'input-pins-v2.json').read_text());checks=[]
for row in pins['inputs']:
 for f in row['files']:
  p=Path(f['path']);checks.append(dict(path=str(p),unchanged=p.is_file() and sha(p)==f['sha256']))
assert all(row['unchanged'] for row in checks)
(P/'post-audit-inputs.json').write_text(json.dumps(dict(all_unchanged=True,files=checks),separators=(',',':'))+'\n')
for p in P.glob('*.json'):shutil.copyfile(p,meta/p.name)
(W/'README.txt').write_text('INCREMENTAL UNTRUSTED CURRENT-SIDE DECLARATION DATA\nReuse the immutable base at '+base['location']+' with manifest SHA256 '+base['manifest_sha256']+'. One newly needed AdapterRwAccepted proof-only dependency is freshly checked at byte-identical published source and strictly identical statement. No baseline constants originate from that module. No unchanged payloads are reserialized here.\nNew source-cut/original-body equivalence/consumer/preparation/challenge-range logical closure. Full type/opaque value/mutual/constructor/recursor terms are retained under original names. Module imports/extraConstNames/extension entries empty.\nThe combined data audit found no missing seeds, unresolved constants or conflicting declarations. THIS IS NOT KERNEL RECONSTRUCTION. Consumer must kernel-check safe logical closure and perform original/current/enclosing ALL14/event/source/release joins.\nThe old raw unsafe reserve compiler auxiliary remains ONLY in the base, is not a proof seed, and must not weaken unsafe/partial rejection. No native memory/Claims/Terminal/security closure claimed.\n')
files=[dict(relative=str(p.relative_to(W)),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(W.rglob('*')) if p.is_file()]
manifest=dict(schema='focused-extractor-proof-packet-v1',kind='incremental-untrusted-raw-declaration-transport',base_location=base['location'],base_manifest_sha256=base['manifest_sha256'],base_transport_modules=basemanifest['transport_modules'],new_transport_modules=len(list((W/'transport').rglob('*.olean'))),incremental_constants=exsummary['constants'],combined_audit=summary,raw_unsafe_or_partial=unsafe,proof_refresh=refresh,ledger=ledger,files=files,scope='Combined hash-pinned closed raw logical data only; no kernel reconstruction, original/current equality, native/SDK/Std/runtime/artifact/security closure.')
(W/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');mb=(W/'manifest.json').read_bytes()
for p in W.rglob('*'):
 if p.is_file():p.chmod(0o444)
for p in sorted([p for p in W.rglob('*') if p.is_dir()],key=lambda p:len(p.parts),reverse=True):p.chmod(0o555)
W.chmod(0o555);W.rename(dest)
(P/'release-manifest.json').write_bytes(mb);(P/'release.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',location=str(dest),manifest_sha256=hashlib.sha256(mb).hexdigest(),incremental_constants=manifest['incremental_constants'],new_transport_modules=manifest['new_transport_modules'],raw_payload_bytes=sum(f['bytes'] for f in files if f['relative'].startswith('transport/')),scope=manifest['scope']),indent=2)+'\n')
print(json.dumps(dict(location=str(dest),constants=manifest['incremental_constants'],new_modules=manifest['new_transport_modules'])))
