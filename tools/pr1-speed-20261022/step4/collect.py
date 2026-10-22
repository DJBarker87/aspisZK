from pathlib import Path
import json,hashlib,re,statistics,sys,shutil
h=Path(sys.argv[1]);stage=sys.argv[2];r=h/('pr1-'+stage);out=Path(sys.argv[3]);out.mkdir(parents=True,exist_ok=True)
log=(r/'receipts'/(stage+'-fixtures')/'stderr.log').read_text();times=[list(map(float,x.split()))for x in re.findall(r'^PR1_TIME (.*)$',log,re.M)];assert len(times)==6
rows=[]
for run in range(3):
 for j,f in enumerate(['transfer','withdrawal']):
  p=r/('fixtures-'+stage)/f'S2-{f}-{run}';meta=json.loads((p/'fixture.json').read_text());assert meta['native_acceptance'] and meta['dense_acceptance']
  hashes={}
  for file in ['proof.bin','public.bin']:
   data=(p/file).read_bytes();assert data==(h/'pr1-baseline/fixtures'/f'S2-{f}-0'/file).read_bytes();hashes[file]=dict(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
  rows.append(dict(fixture=f,run=run,p_r1_seconds=times[2*run+j][-1],phases_seconds=times[2*run+j][:-1],end_to_end_seconds=meta['prover_wall_seconds'],identity=hashes))
med={f:{key:statistics.median(x[key]for x in rows if x['fixture']==f)for key in ['p_r1_seconds','end_to_end_seconds']}for f in ['transfer','withdrawal']}
base=json.loads((h/'pr1-baseline/challenges.json').read_text());new=json.loads((r/('challenges-'+stage+'.json')).read_text());assert len(base)==len(new)==1000;assert [(x['input_sha256'],x['accepted'])for x in base]==[(x['input_sha256'],x['accepted'])for x in new]
result=dict(stage=stage,samples=rows,medians=med,challenge_count=1000,accepts=sum(x['accepted']for x in new),mismatches=0)
(out/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
for p in (r/'receipts').glob(stage+'*/receipt.json'):shutil.copytree(p.parent,out/'receipts'/p.parent.name,dirs_exist_ok=True)
for p in r.glob('reservation-'+stage+'*.json'):shutil.copy(p,out/p.name)
shutil.copy(r/('challenges-'+stage+'.json'),out/'challenges.json')
print(json.dumps(med,indent=2))
