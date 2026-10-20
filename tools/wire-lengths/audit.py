"""Audit the final sources against recorded successful compilations, without replay."""
import pathlib, hashlib, json, re
root=pathlib.Path(__file__).resolve().parents[2]
base=root/'docs/research/100bit-spend-path-20261013'
ev=base/'evidence/wire-lengths-20261019'
rows=[]
for src in sorted((base/'lean').glob('BinWire*Lengths.lean')):
 sha=hashlib.sha256(src.read_bytes()).hexdigest()
 candidates=[(p,json.loads(p.read_text())) for p in (ev/src.stem).glob('attempt-*/receipt.json')]
 matches=[(p,r) for p,r in candidates if r['exit_status']==0 and r['source_sha256']==sha]
 assert len(matches)==1,(src,matches)
 p,r=matches[0]
 theorem_count=len(re.findall(r'^theorem ',src.read_text(),re.M))
 assert theorem_count==len(r['axioms']),(src,theorem_count,r['axioms'])
 assert not r['errors'] and r['process_swap_count']==0
 assert all('sorryAx' not in a for a in r['axioms'])
 for a in r['axioms']:
  names=re.search(r'\[([^\]]*)\]',a)
  assert not names or set(x.strip() for x in names[1].split(',')) <= {'propext','Classical.choice','Quot.sound'}
 # Snapshot only when the source matches the receipt (never reconstruct failed inputs).
 (p.parent/'source.lean').write_bytes(src.read_bytes())
 rows.append({'module':src.stem,'receipt':str(p.relative_to(root)),'source_sha256':sha,'theorems':theorem_count,'wall_seconds':r['wall_seconds'],'peak_rss_bytes':r['peak_rss_bytes'],'swaps':r['process_swap_count']})
j=[json.loads(x) for x in (ev/'j-attempts.jsonl').read_text().splitlines()]
src=root/'docs/research/v8-r0-zk-20261009/lean/R1Z/WireLengthsR1PBin.lean'
sha=hashlib.sha256(src.read_bytes()).hexdigest()
good=[r for r in j if r['exit']==0 and r['module']=='R1Z.WireLengthsR1PBin' and r['source_sha256']==sha]
assert len(good)==1
assert len(good[0]['axioms'])==len(re.findall(r'^theorem ',src.read_text(),re.M))==5
assert all('sorryAx' not in a for a in good[0]['axioms'])
assert good[0]['swaps']==0
assert {r['attempt'] for r in j}==set(range(6250,6256))
assert all(r['exit']==67 for r in j if r['attempt']>=6252)
(ev/'audit.json').write_text(json.dumps({'status':'pass','local_final':rows,'local_theorems':sum(r['theorems'] for r in rows),'privacy_final':good[0],'root_refusals':[r['module'] for r in j if r['exit']==67]},indent=2)+'\n')
# Re-index all local attempts, including historical failures.
manifest={'schema':'focused-extractor-proof-packet-v1','source_revision_parent':good[0]['source_revision_parent'],'attempts':[json.loads(p.read_text()) for p in sorted(ev.glob('*/attempt-*/receipt.json'))],'final_successes':rows,'audit':'audit.json','privacy_attempts':'j-attempts.jsonl'}
(ev/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('PASS:',sum(r['theorems'] for r in rows),'local + 5 privacy theorem audits; 4 fingerprint refusals')
