"""Read-only immutable sibling intake; no proof or build invocation."""
from pathlib import Path
import subprocess,json,hashlib,re
E=Path(__file__).resolve().parent
REV='4a3159e771cc13cdf34a40dec53d669c2eeebd88'
BASE='evidence/slice-q-compose6-20261104/'
sha=lambda b:hashlib.sha256(b).hexdigest()
def blob(p):return subprocess.check_output(['git','show',REV+':'+p])
def obj(p):return json.loads(blob(BASE+p))
manifest=obj('NFG_HANDOFF_MANIFEST.json'); checked=[]
p=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
for f in manifest['files']:
 p.stdin.write((REV+':'+f['path']+'\n').encode());p.stdin.flush()
 head=p.stdout.readline().decode().split();assert head[1]=='blob',head
 b=p.stdout.read(int(head[2]));assert p.stdout.read(1)==b'\n'
 assert len(b)==f['bytes'] and sha(b)==f['sha256'],f['path']
 checked.append(dict(path=f['path'],blob=head[0],sha256=sha(b),bytes=len(b)))
p.stdin.close();assert p.wait()==0
pack=obj('NFG_PACKETS.json');cert=obj('NFG_CERTIFICATES.json')
want={'TX1:111','TX2:077','TX1:108','TX2:074'}
selected=[c for c in cert if c['row'] in want];assert {c['row'] for c in selected}==want
for c in selected:
 assert c['remaining_inner_hypotheses']==[] and c['packet_sha256']==sha(blob(BASE+'NFG_PACKETS.json'))
 assert all(o['status']=='CLOSED' for o in c['call_obligations'])
 assert c['frozen_body_sha256'] in {r['body_sha256'] for r in pack['source']['roots']}
for proof in pack['proofs']:
 r=obj(proof['attempt']+'/receipt.json')
 assert r['exit_status']==0 and r['module']==proof['module']
 assert sha(blob(BASE+proof['module']+'.lean'))==proof['source_sha256']
 assert sha(blob(BASE+proof['attempt']+'/receipt.json'))==proof['receipt_sha256']
 for line in proof['axioms']:
  m=re.fullmatch(r"'[^']+' depends on axioms: \[(.*)\]",line)
  assert m is not None,line
  assert {x.strip() for x in m[1].split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'},line
 assert r['limits']['memory.max']=='8589934592' and r['limits']['memory.swap.max']=='0'
combined=obj('NFG_L077/receipt.json');assert combined['exit_status']==0
library=obj('NFG_PEER_LIBRARY_COMPARISON.json');assert not library['different']
# Own proof sources remain the only members of the NFM combined kernel import.
# These are immutable reference snapshots, not new modules or newly claimed builds.
files=['NFG_HANDOFF.md','NFG_REMAINING.md','NFG_COMPOSED.md','NFG_CERTIFICATES.json','NFG_PACKETS.json','NFG_PEER_LIBRARY_COMPARISON.json','NFG_LPh_STUBS.md']+[q['module']+'.lean' for q in pack['proofs']]
D=E/'NFM_peer_inputs';D.mkdir(exist_ok=True);copies=[]
for name in files:
 b=blob(BASE+name);target=D/(name+'.txt' if name.endswith('.lean') else name)
 target.write_bytes(b);copies.append(dict(source=BASE+name,destination=str(target.relative_to(E)),revision=REV,sha256=sha(b)))
out=dict(schema='NFM-immutable-peer-intake-v1',revision=REV,closure_commit=manifest['closure_commit'],manifest_sha256=sha(blob(BASE+'NFG_HANDOFF_MANIFEST.json')),checked_files=checked,copies=copies,callee_certificates=selected,proof_receipts_checked=len(pack['proofs']),combined_receipt_sha256=sha(blob(BASE+'NFG_L077/receipt.json')),library_comparison=library,status='PASS_IMMUTABLE_EXISTING_CALLEE_INTAKE',scope='Existing independently validated push packets only; no new NFM row credit; no NEW/NFB geometry import; no claim of a new combined kernel replay with NFG. NFM combined audit remains its 124 recorded roots.',validation='Every sibling manifest byte hash checked from immutable Git; all packet proof source/receipt hashes, exits, axioms, caps and selected certificate completeness rechecked. Native packet receipts remain the sibling validation, not new runs.')
(E/'NFM_PEER_INTAKE.json').write_text(json.dumps(out,indent=1)+'\n');print(out['status'],len(checked),'files;',len(copies),'reference snapshots')
