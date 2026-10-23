#!/usr/bin/env python3
"""Export native post-first cuts and failed approaches, source/text only."""
from pathlib import Path
import json,hashlib,shutil,tomllib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');O=H/'sdk-native-tail-export-v1';O.mkdir(exist_ok=True)
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def copy(p,r):
 q=O/r;q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
accepted={};excluded={}
for receipt in sorted((H/'receipts').glob('sdk-native-*/receipt.json')):
 tag=receipt.parent.name
 if not ('post-first-tail' in tag or 'tail-leaf-links' in tag or 'tail-write-frame' in tag or 'tail-modular-frame' in tag or 'native-success' in tag):continue
 r=load(receipt);ip=H/(tag+'-input.json')
 if not ip.exists():continue
 i=load(ip);P=Path(r['cwd'])
 if 'sdk-native-success-root2-v' in tag:P=H/('sdk-shared-prefix-'+tag.removeprefix('sdk-'))
 if not (P/'src/lib.rs').is_file():continue
 for rel in ['src/lib.rs','Cargo.toml','Cargo.lock','source-cut.json']:
  if (P/rel).is_file():copy(P/rel,Path('sources')/P.name/rel)
 for p in receipt.parent.iterdir():
  if p.is_file() and p.suffix in ['.json','.log']:copy(p,Path('receipts')/tag/p.name)
 for suffix in ['-input.json','-admission.json','-dependency-postcheck.json']:
  if (H/(tag+suffix)).exists():copy(H/(tag+suffix),tag+suffix)
 for p in (H/tag).glob('*'):
  if p.is_file() and p.suffix in ['.json','.log','.c','.py']:copy(p,Path('cases')/tag/p.name)
 row=dict(target=tag,source=P.name,source_sha256=sha(P/'src/lib.rs'),receipt_sha256=sha(receipt),exit_status=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'])
 if r['exit_status']==0 and tag in ['sdk-native-post-first-tail-root1-check-v5','sdk-native-post-first-tail-root2-check-v5','sdk-native-post-first-tail-root0-window0-check-v6','sdk-native-tail-leaf-links-check-v1']:
  assert r['swaps']==0 and 'VERIFICATION:- SUCCESSFUL' in (receipt.parent/'stdout.log').read_text()
  import re
  row['assertions']=int(re.search(r'0 of (\d+) failed',(receipt.parent/'stdout.log').read_text())[1])
  matches=[]
  for p in (H/'target/kani').rglob('*.kani-metadata.json'):
   for h in load(p).get('proof_harnesses',[]):
    if h['pretty_name']=='proofs::native_post_first_tail' and h['crate_name']==tomllib.loads((P/'Cargo.toml').read_text())['package']['name'].replace('-','_'):matches.append((p,h))
  assert len(matches)==1,(tag,len(matches))
  p,h=matches[0];copy(p,Path('metadata')/tag/'harness-metadata.json');raw=Path(h['goto_file']);prepared=Path(str(raw).replace('.symtab.out','.out'))
  row['raw_goto_sha256']=sha(raw);row['prepared_goto_sha256']=sha(prepared)
  assert h['attributes']['kind']=='Proof' and not h['attributes']['stubs']
  accepted[tag]=row
 else:excluded[tag]=row
 for package,pin in i.get('local_dependency_source_pins',{}).items():
  root=Path(pin['root'])
  for rel,d in pin['files'].items():
   assert sha(root/rel)==d;copy(root/rel,Path('dependencies')/package/rel)
for root in [1,2]:
 tag=f'sdk-native-post-first-tail-root{root}-check-v5'
 audit=H/(tag+'-audit-v2')
 for p in audit.iterdir():
  if p.is_file() and p.suffix in ['.json','.log']:copy(p,Path('cover-audits')/str(root)/p.name)
 for qtag in [tag+'-inventory',tag+'-covers-v2']:
  for p in (H/'receipts'/qtag).iterdir():
   if p.is_file() and p.suffix in ['.json','.log']:copy(p,Path('receipts')/qtag/p.name)
  for suffix in ['-input.json','-admission.json','-dependency-postcheck.json']:
   if (H/(qtag+suffix)).is_file():copy(H/(qtag+suffix),qtag+suffix)
for n in ['run-modular-host.py','capped.py','reservation.py','audit-native-tail-covers-host.py','prepare-native-success-host.py','run-native-success-host.py']:
 if (H/'kit'/n).is_file():copy(H/'kit'/n,Path('runner')/n)
(O/'qualification.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',accepted=accepted,excluded=excluded,scope='Actual original SDK post-first cuts with real std Ref/RefMut, exact full statement Box and declaration/Drop order; checked encoded_finish is sole verified callee stub, retains original native_finish/full ProgramError. Initial slot/counter facts come from first-entry certificates; reply is mapped first result, all lengths0..1769. Root1/2 complete point domains pass; root0 only window0, not full proof frame. Leaf-links asserts actual guard-counter/copy-destination and disjoint regions, not whole caller frame.',covers='CLI main reports3of5 covers; five locations include three compiler copies of same wrong-length intention. Root1/2 targeted audits prove all3 distinct source intentions reached. Raw inventory noncover count differs enabled Kani counts; only original assertion run is proof gate. No extra cover claim for root0 or leaf-links.',remaining='Concrete checked-leaf/source/caller composition, owner deallocation/runtime heap mapping, actual child/gate/scan installation, ordered oracle/errors/log transport and TX2 retention/reconstruction. Failed/timeout approaches excluded; source-only focused compilation, no whole S2/TOTAL/soundness claim.'),indent=2)+'\n')
(O/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files={str(p.relative_to(O)):sha(p) for p in O.rglob('*') if p.is_file() and p.name!='manifest.json'}),indent=2)+'\n')
print(json.dumps(dict(output=str(O),accepted=len(accepted),excluded=len(excluded))))
