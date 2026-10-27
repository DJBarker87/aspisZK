from pathlib import Path
import json,hashlib,re,collections
E=Path(__file__).resolve().parent;R=E.parents[1];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();load=lambda p:json.loads(p.read_text())
p=load(E/'RPu_plan.json');checks=[]
for row in p['rows']:
 old=R/row['original_source'];new=R/row['source'];assert sha(old)==row['original_sha256'];assert sha(new)==row['sha256']
 canon=lambda s:re.sub(r'^import .*\n','',s,flags=re.M)
 assert canon(old.read_text())==canon(new.read_text()),row['original']
 checks.append({'original':row['original'],'original_sha256':sha(old),'snapshot_sha256':sha(new),'only_imports_changed':True})
(E/'RPu_source-check.json').write_text(json.dumps(checks,indent=2)+'\n')
pins=[]
paths=['evidence/replay-tops1-20261027/RPt_LEDGER.md']
for job,n in [('finish-match4','FJp'),('finish-chain1','FJu'),('stack1','FJv')]:
 for f in (R/f'evidence/{job}-20261027').glob(n+'_*'):
  if f.is_file() and ('statement' in f.name.lower() or 'recount' in f.name or 'kernel' in f.name or 'before.lean' in f.name or 'after.lean' in f.name or 'HANDOFF' in f.name):paths.append(str(f.relative_to(R)))
for path in paths:
 f=R/path;pins.append({'path':path,'sha256':sha(f),'bytes':f.stat().st_size})
(E/'RPu_job-evidence-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
statements=[]
for root,job,n in [('FJp_Top','finish-match4','FJp'),('FJu_Top','finish-chain1','FJu')]:
 s=(R/'lean'/(root+'.lean')).read_text();s=s[s.index('theorem deployed'):];s=s[:s.index(':= by')].strip()+'\n';f=R/f'evidence/{job}-20261027/{n}_after.lean.txt';assert s.rstrip()==f.read_text().rstrip(),root
 (E/f'RPu_{root}.source-statement.txt').write_text(s)
 statements.append({'root':root,'source_statement_sha256':hashlib.sha256(s.encode()).hexdigest(),'job_statement':str(f.relative_to(R)),'byte_identical':s.encode()==f.read_bytes(),'identical_after_trailing_whitespace_normalization':s.rstrip()==f.read_text().rstrip()})
for root in ['FJv_Top','FJv_Deployed']:
 s=(R/'lean'/(root+'.lean')).read_text();s=s[s.index('theorem deployed'):];s=s[:s.index(':= by')].strip()+'\n';(E/f'RPu_{root}.source-statement.txt').write_text(s)
(E/'RPu_source-statement-comparison.json').write_text(json.dumps(statements,indent=2)+'\n')
# Recompute predecessor ledgers from atomic rows, preserving their status/scope.
results=[]
for path in ['evidence/finish-match4-20261027/FJp_recount.json','evidence/finish-chain1-20261027/FJu_recount.json','evidence/stack1-20261027/FJv_recount.json']:
 d=load(R/path)
 for stage in d.get('steps',[d]):
  counts=collections.defaultdict(lambda:dict(T=0,P=0,G=0,C=0))
  for row in stage['rows']:
   if row['status'] in ['removed','discharged']:continue
   scope=row['scope'];cls=row['classification']
   if cls not in ['T','P','G','C']:continue
   counts[scope][cls]+=1
  actual=counts['actual antecedent'];deploy=counts['deployment only'];inclusive={k:actual[k]+deploy[k] for k in actual}
  assert actual==stage['after_counts']['actual antecedent'],(path,actual)
  assert inclusive==stage['after_counts']['deployment-inclusive non-alias'],(path,inclusive)
  results.append({'path':path,'sha256':sha(R/path),'top':stage.get('top',d.get('after')),'actual':actual,'deployment_only':deploy,'inclusive_non_alias':inclusive,'replay_delta':dict(T=0,P=0,G=0,C=0)})
(E/'RPu_ledger-check.json').write_text(json.dumps(results,indent=2)+'\n')
print('import-only snapshots',len(checks),'source statements match original evidence',len(statements),'atomic recounts',len(results))
