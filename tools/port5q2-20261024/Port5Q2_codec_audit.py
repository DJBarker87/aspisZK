#!/usr/bin/env python3
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/port5q2-20261024';old=R/'evidence/ports3-20261023';rows=[]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n in [6,7]:
 p=old/f'kani-{n:03d}/receipt.json';r=json.loads(p.read_text());assert r['exit_status']==0
 assert 'VERIFICATION SUCCESSFUL' in (p.parent/'stdout.log').read_text()
 pins=r['deps_fingerprint']['source_snapshot_pins'];assert all(sha(R/k)==v for k,v in pins.items())
 name='writer-reached/src/lib.rs';snap=p.parent/'sources'/name;assert sha(snap)==r['source_hashes'][name]
 current=(R/'tools/ports3-20261023/writer-reached/src/lib.rs').read_text();historical=snap.read_text()
 assert current.split('#[cfg(kani)] mod proofs',1)[0]==historical.split('#[cfg(kani)] mod proofs',1)[0]
 rows.append({'receipt':str(p.relative_to(R)),'receipt_sha256':sha(p),'target':r['command'][r['command'].index('--harness')+1],'source_revision':r['source_revision'],'exit_status':r['exit_status'],'wall_seconds':r['wall_seconds'],'peak_rss_kib':r['peak_rss_kib'],'swaps':r['swaps'],'print_axioms':r['print_axioms'],'source_pin_count':len(pins),'domain':'arbitrary exact16/32 byte array; same current scalar codec sources and helper definitions; no whole reader result','current_model_relation':'All pre-harness definitions byte-identical; retained scalar harness source pinned independently'})
(E/'codec-admission.json').write_text(json.dumps({'schema':'port5q2-reused-native-codec-contracts-v1','contracts':rows,'new_kani_runs':0,'excluded_whole_reader_attempts':['evidence/ports3-20261023/kani-005','evidence/ports3-20261023/kani-008']},indent=2)+'\n')
print('PASS: two retained scalar codec contracts; no Kani replay')
