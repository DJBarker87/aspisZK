#!/usr/bin/env python3
"""Publish an owning-session untrusted read-only transport, never a proof result."""
from pathlib import Path
import hashlib,json,shutil,subprocess,os
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';P=E/'sdk-current-export-20261024';W=Path('/private/tmp/s126-sdk-current-export-20261024-v2');dest=Path('/private/tmp/aspis-released/s126-sdk-current-9acc-proof-refresh-20261024-v1')
assert W.exists() and not dest.exists()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source_ledger={}
for attempt in ['sdk-current-export-v1','sdk-current-transport-audit-v1','sdk-current-transport-audit-v2','sdk-current-transport-audit-v3','sdk-current-entry-privileges-replay-v1','sdk-current-export-v2','sdk-current-transport-audit-v4']:
 r=json.loads((E/attempt/'receipt.json').read_text());source_ledger[attempt]={k:r[k] for k in ['target','source_revision','source_sha256','exit_status','wall_seconds','peak_rss_bytes','swaps','print_axioms']}
for a in ['sdk-current-entry-privileges-replay-v1','sdk-current-export-v2','sdk-current-transport-audit-v4']:
 assert source_ledger[a]['exit_status']==0 and source_ledger[a]['swaps']==0
export_lines=(E/'sdk-current-export-v2/lean.log').read_text().splitlines();audit_lines=(E/'sdk-current-transport-audit-v4/lean.log').read_text().splitlines()
parse=lambda lines,prefix:json.loads(next(l[len(prefix):] for l in lines if l.startswith(prefix)))
assert parse(export_lines,'UNRESOLVED ')==[]
summary=parse(audit_lines,'AUDIT_SUMMARY ');assert summary['unresolved']==[] and summary['missing_seeds']==[] and summary['conflicts']==0
refresh=[json.loads(l[len('PROOF_REFRESH '):]) for l in audit_lines if l.startswith('PROOF_REFRESH ')];assert len(refresh)==4 and all(r['same_type'] and r['old_theorem'] and r['new_theorem'] for r in refresh)
unsafe=[json.loads(l[len('UNSAFE_OR_PARTIAL '):]) for l in audit_lines if l.startswith('UNSAFE_OR_PARTIAL ')];assert unsafe==['AspisR1.S2W_D189Wrappers.reserve._unsafe_rec']
post={}
for label in ['input-pins.json','input-pins-v2.json']:
 m=json.loads((P/label).read_text());ok=all(sha(Path(f['path']))==f['sha256'] for row in m['inputs'] for f in row['files']);assert ok;post[label]=dict(all_unchanged=True,sha256=sha(P/label),modules=len(m['inputs']))
seeds=parse(export_lines,'SEEDS ');request=json.loads((P/'request.json').read_text());assert set(request['primary_seeds'])<=set(seeds)
meta=W/'metadata';meta.mkdir();logs=W/'logs';logs.mkdir()
for p in P.glob('*.json'):shutil.copyfile(p,meta/p.name)
for a in source_ledger:
 for n in ['source.lean','command.json','receipt.json','time.log']:
  q=E/a/n
  if q.exists():shutil.copyfile(q,meta/(a+'-'+n))
 # Large derived logs remain outside Git, intact and explicitly hashed.
 shutil.copyfile(E/a/'lean.log',logs/(a+'.log'))
# Historical producer evidence is distinct from the fresh export checks.
accepted=json.loads((E/'accepted-targets.json').read_text())['targets']
for n in request['targets']:
 r=E/accepted[n]['receipt'];shutil.copyfile(r,meta/(n+'-historical-receipt.json'))
# Exact raw transport payload and current-side edges/duplicate/conflict evidence.
(W/'edges.jsonl').write_text('\n'.join(l[len('EDGE '):] for l in export_lines if l.startswith('EDGE '))+'\n')
(W/'constants.jsonl').write_text('\n'.join(l[len('CONSTANT '):] for l in audit_lines if l.startswith('CONSTANT '))+'\n')
(W/'duplicates.jsonl').write_text('\n'.join(l[len('DUPLICATE '):] for l in audit_lines if l.startswith('DUPLICATE '))+'\n')
(W/'conflicts.jsonl').write_text('\n'.join(l[len('CONFLICT_FULL '):] for l in audit_lines if l.startswith('CONFLICT_FULL ')))
(W/'README.txt').write_text('UNTRUSTED CURRENT-SIDE RAW DECLARATION TRANSPORT\nPrimary source/object seeds are 9acc015544. ONE proof-only dependency is freshly replayed against the current model. This is NOT the unchanged historical 9acc closure.\nImports/entries/extraConstNames empty; exact constants/constNames/full values preserved. No declaration is trusted by this export. Consumer must kernel-check the selected safe logical closure, compare against original-side declarations, and retain all conditional premises.\nThe raw complete factor also contains reserve._unsafe_rec, a generated compiler auxiliary. It is retained as requested raw data, is not a logical proof seed, and must not bypass the consumer unsafe/partial rejection.\nOriginal RootS2 side is not included/relabelled. Exact original export failure with two missing project helpers remains in the source-only ledger.\n')
files=[dict(relative=str(p.relative_to(W)),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(W.rglob('*')) if p.is_file()]
manifest=dict(schema='focused-extractor-proof-packet-v1',kind='untrusted-raw-declaration-transport',status='released-proof-refresh-overlay',immutable_location=str(dest),primary_source_revision=request['current_revision'],request_revision='93de4606f3',transport_modules=summary['modules'],constant_count=summary['constants'],duplicate_count=summary['duplicates'],nonidentical_current_duplicates=0,unresolved=[],missing_seeds=[],proof_refresh=refresh,raw_unsafe_or_partial=unsafe,seed_count=len(seeds),post_input_checks=post,ledger=source_ledger,files=files,scope='Closed CURRENT-side raw transport with an explicit same-statement proof-only import refresh; no kernel reconstruction, original/current agreement, source/Rust/SBF identity or security closure is claimed.')
(W/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n');manifest_bytes=(W/'manifest.json').read_bytes()
# Publish by one rename, with read-only mode on every retained file/directory.
for p in W.rglob('*'):
 if p.is_file():p.chmod(0o444)
for p in sorted((p for p in W.rglob('*') if p.is_dir()),key=lambda p:len(p.parts),reverse=True):p.chmod(0o555)
W.chmod(0o555);dest.parent.mkdir(mode=0o755,parents=True,exist_ok=True);W.rename(dest)
(P/'release-manifest.json').write_bytes(manifest_bytes)
(P/'release.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',location=str(dest),manifest_sha256=hashlib.sha256(manifest_bytes).hexdigest(),manifest_bytes=len(manifest_bytes),raw_payload_bytes=sum(f['bytes'] for f in files if f['relative'].startswith('transport/')),derived_artifacts=[f for f in files if f['relative'].endswith('.jsonl') or f['relative'].startswith('logs/')],summary=summary,proof_refresh=refresh,raw_unsafe_or_partial=unsafe,post_input_checks=post,scope=manifest['scope']),indent=2)+'\n')
(P/'ledger.json').write_text(json.dumps(source_ledger,indent=2)+'\n')
print(json.dumps(dict(location=str(dest),summary=summary,raw_payload_bytes=sum(f['bytes'] for f in files if f['relative'].startswith('transport/')))))
