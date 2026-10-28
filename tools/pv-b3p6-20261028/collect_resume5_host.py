"""Archive this resume's receipts and exact successful LLBC input snapshots."""
from pathlib import Path
import json,hashlib,lzma,shutil
from run import H
O=H/'archive-resume5';O.mkdir(exist_ok=True);R=O/'receipts-resume5';R.mkdir(exist_ok=True);L=O/'llbc-resume5';L.mkdir(exist_ok=True);index=[]
labels=sorted(set(H.glob('charon227-resume5*'))|set(H.glob('aeneas227-resume5*'))|set(H.glob('native227-resume5-owned*'))|set(H.glob('fidelity227-resume5-native'))|set(H.glob('lean-420[0-9][0-9]*')))
for p in labels:
 if not p.is_dir():continue
 q=R/p.name;q.mkdir(exist_ok=True)
 for f in p.rglob('*'):
  if not f.is_file() or f.suffix in ['.olean','.ilean']:continue
  dest=q/f.relative_to(p);dest.parent.mkdir(exist_ok=True,parents=True);shutil.copy2(f,dest)
 receipt=p/'receipt/receipt.json'
 if not receipt.exists():continue
 r=json.loads(receipt.read_text());item=dict(label=p.name,receipt='receipts-resume5/'+p.name+'/receipt/receipt.json',exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],recorded_source_revision=r['source_revision'],print_axioms=r['print_axioms'])
 command=r['command'];llbc=None
 if '--dest-file'in command:llbc=Path(command[command.index('--dest-file')+1])
 elif p.name.startswith('aeneas'):llbc=Path(command[-1])
 if llbc and llbc.exists():
  raw=llbc.read_bytes();x=json.loads(raw);out=L/(llbc.name+'.xz')
  if not out.exists():
   with lzma.open(out,'wb')as z:z.write(raw)
   (L/(llbc.name+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n')
  source_inputs={str(f['name']):hashlib.sha256(f['contents'].encode()).hexdigest()for f in x['translated']['files']if f.get('contents')is not None}
  item['extraction_input']=dict(llbc=str(out.relative_to(O)),uncompressed_sha256=hashlib.sha256(raw).hexdigest(),size=len(raw),source_inputs=source_inputs,charon_options=x['translated']['options'],has_errors=x['has_errors'])
  item['revision_correction']='Recorded source revision pins frozen deployed sources; owned proof-only inputs were edited between gates. Exact owned source bytes are in LLBC files.contents and identified above; no attribution of those edits to the recorded older commit.'
 index.append(item)
(O/'receipt-index-resume5.json').write_text(json.dumps(index,indent=2)+'\n')
for name in ['TALLY-resume5.json','external-verification-resume5.json','project-resolution-resume5.json','native227-resume5-features.json','fidelity227-resume5-features.json','native227-parts-features.json','native227-parts-features-original-revision-label.json','aeneas-root-preflight227.json','native227-composition-features.json','fidelity227-resume5-features-original-revision-label.json','native227-composition-source-freeze.json']:
 if (H/name).exists():shutil.copy2(H/name,O/name)
print(json.dumps(dict(receipts=len(index),archive=str(O))))
