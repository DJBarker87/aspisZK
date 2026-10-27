from pathlib import Path
import json,hashlib,re,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
records=[];passed={}
for attempt in sorted(P.glob('JGq_TX2_[0-9][0-9][0-9]')):
 receipt=attempt/'receipt.json'
 if not receipt.exists():continue
 d=json.loads(receipt.read_text());stdout=(attempt/'stdout.log').read_text()
 row={k:d.get(k) for k in ['attempt','command','sources','source_revision','source_tree_dirty','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','cgroup','limits','cgroup_memory_peak_bytes','print_axioms']}
 row['errors']=[line for line in stdout.splitlines() if re.search(r'error(?::|\()',line)]
 row['receipt']=str(receipt.relative_to(R));records.append(row)
 if d['exit_status']==0:
  assert 'sorryAx' not in stdout
  for line in d['print_axioms']:
   if 'depends on axioms: [' in line:
    assert set(line.split('depends on axioms: [')[1].split(']')[0].replace('\n','').split(', '))<=set(['propext','Classical.choice','Quot.sound']),line
  for f,h in d['source_hashes'].items():passed[f,h]=d['attempt']
validation={}
for p in sorted((R/'lean').glob('JGq_*.lean')):
 h=hashlib.sha256(p.read_bytes()).hexdigest();a=passed.get((p.name,h));validation[p.name]={'sha256':h,'passing_attempt':a}
(P/'JGq_ATTEMPTS.jsonl').write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in records))
(P/'JGq_VALIDATION.json').write_text(json.dumps(validation,indent=2)+'\n')
summary={'lean_processes':len(records),'pass':sum(r['exit_status']==0 for r in records),'reject':sum(r['exit_status']!=0 for r in records),'kani_runs':0,'lean_wall_seconds':sum(r['wall_seconds'] for r in records),'max_peak_rss_kib':max([int(r['peak_rss_kib']) for r in records]+[0]),'swaps':sum(int(r['swaps']) for r in records),'current_checked_sources':sum(bool(d['passing_attempt']) for d in validation.values()),'current_unchecked_sources':sum(not d['passing_attempt'] for d in validation.values())}
assert len(records)<=100
(P/'JGq_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary))
