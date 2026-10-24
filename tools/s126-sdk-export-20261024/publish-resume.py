#!/usr/bin/env python3
"""Recover publication into a unique owner path; never alter shared read-only roots."""
from pathlib import Path
import hashlib,json,shutil,time,resource,os
R=Path(__file__).resolve().parents[2];P=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/sdk-current-export-20261024'
W=Path('/private/tmp/s126-sdk-current-export-20261024-v2');stage=Path('/private/tmp/s126-sdk-release-publish-20261024-v1');dest=Path('/private/tmp/s126-sdk-current-9acc-proof-refresh-20261024-v1');assert not stage.exists() and not dest.exists()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();start=time.monotonic();m=json.loads((W/'manifest.json').read_text());old=sha(W/'manifest.json');stage.mkdir(mode=0o700)
for row in m['files']:
 src=W/row['relative'];assert src.is_file() and not src.is_symlink() and src.stat().st_size==row['bytes'] and sha(src)==row['sha256']
 out=stage/row['relative'];out.parent.mkdir(mode=0o700,parents=True,exist_ok=True);shutil.copyfile(src,out);assert sha(out)==row['sha256']
m['immutable_location']=str(dest);m['publication_history']=dict(failed_destination='/private/tmp/aspis-released/s126-sdk-current-9acc-proof-refresh-20261024-v1',exception='PermissionError at final rename into existing read-only shared parent',retained_failed_manifest_path=str(W/'manifest.json'),retained_failed_manifest_sha256=old,recovery='New owned staging and unique /private/tmp destination; no shared directory/cache permissions or existing exports altered.')
(stage/'manifest.json').write_text(json.dumps(m,indent=2)+'\n');body=(stage/'manifest.json').read_bytes()
for p in stage.rglob('*'):
 if p.is_file():p.chmod(0o444)
for p in sorted((p for p in stage.rglob('*') if p.is_dir()),key=lambda p:len(p.parts),reverse=True):p.chmod(0o555)
stage.chmod(0o555);stage.rename(dest)
(P/'release-manifest.json').write_bytes(body)
(P/'release.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',location=str(dest),manifest_sha256=hashlib.sha256(body).hexdigest(),manifest_bytes=len(body),raw_payload_bytes=sum(f['bytes'] for f in m['files'] if f['relative'].startswith('transport/')),derived_artifacts=[f for f in m['files'] if f['relative'].endswith('.jsonl') or f['relative'].startswith('logs/')],summary=dict(modules=m['transport_modules'],constants=m['constant_count'],duplicates=m['duplicate_count'],conflicts=m['nonidentical_current_duplicates'],unresolved=m['unresolved'],missing_seeds=m['missing_seeds']),proof_refresh=m['proof_refresh'],raw_unsafe_or_partial=m['raw_unsafe_or_partial'],post_input_checks=m['post_input_checks'],publication_history=m['publication_history'],scope=m['scope']),indent=2)+'\n')
(P/'ledger.json').write_text(json.dumps(m['ledger'],indent=2)+'\n')
u=resource.getrusage(resource.RUSAGE_SELF);(P/'publication-receipt.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',command=['python3','tools/s126-sdk-export-20261024/publish-resume.py'],source_revision=os.popen('git rev-parse HEAD').read().strip(),source_sha256=sha(Path(__file__)),exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,swaps=u.ru_nswap,print_axioms='N/A: file publication only',scope='No compiler, proof, kernel reconstruction or original-side donor access.'),indent=2)+'\n')
print(json.dumps(dict(location=str(dest),constants=m['constant_count'],modules=m['transport_modules'],raw_payload_bytes=sum(f['bytes'] for f in m['files'] if f['relative'].startswith('transport/')))))
