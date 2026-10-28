from pathlib import Path
import subprocess,json,time,sys,hashlib
D=Path(__file__).resolve().parent
assert (D/'stage-a-complete.json').exists(),'Stage A has not passed'

def run(root,label,args):
 for i in range(11):
  name=label if i==0 else label+'-retry-%02d'%i
  with (root/(name+'-driver.log')).open('w') as f:r=subprocess.run(['python3',str(root/'native.py'),name,*args],stdout=f,stderr=subprocess.STDOUT)
  print(name,r.returncode,flush=True)
  if r.returncode==0:return root/name
  refused=any(p.exists() and not json.loads(p.read_text()).get('allowed',False) for p in [root/name/'reservation.json',root/name/'admission-barrier.json'])
  if not refused:raise SystemExit(r.returncode)
  if i==10:raise SystemExit('Ten refusal retries exhausted')
  time.sleep(180)
roots={'control':D/'combined/baseline','candidate':D}
pins={}
for w,root in roots.items():
 out=run(root,'build-timing',['cargo','build','--release','--offline','--locked','-j','4','-p','aspis-r1-cost-probe','--example','prover_rw_gate','--features','optimized-terminal,r1p-check,ct-host-prover'])
 b=root/'bin/prover_rw_gate';pins[w]=dict(sha256=hashlib.sha256(b.read_bytes()).hexdigest(),bytes=b.stat().st_size,source_revision=(root/'source-revision.txt').read_text().strip(),build_receipt=str(out/'receipt/receipt.json'))
(D/'timing-binary-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
for w,root in roots.items():run(root,'preflight-99',[str(root/'bin/prover_rw_gate'),str(D/'preflight'/w),'99','1'])
rows=[]
sha=lambda b:hashlib.sha256(b).hexdigest()
for fixture in ['transfer','withdrawal']:
 roots={w:D/'preflight'/w/(fixture+'-99') for w in pins}
 files={}
 for name in ['proof.bin','public.bin']:
  bs={w:(p/name).read_bytes() for w,p in roots.items()};files[name]=dict(identical=len(set(bs.values()))==1,**{w:dict(sha256=sha(b),bytes=len(b)) for w,b in bs.items()})
 records={w:json.loads((p/'result.json').read_text()) for w,p in roots.items()}
 canonical={w:json.dumps({k:v for k,v in r.items() if k!='seconds'},sort_keys=True,separators=(',',':')) for w,r in records.items()}
 ledgers={w:{str(q.relative_to(p/'ledger')):dict(sha256=sha(q.read_bytes()),bytes=q.stat().st_size) for q in (p/'ledger').rglob('*') if q.is_file()} for w,p in roots.items()}
 rows.append(dict(fixture=fixture,coin=99,files=files,records=records,canonical_identical=len(set(canonical.values()))==1,ledger_identical=ledgers['control']==ledgers['candidate'],ledger_manifest=ledgers))
passed=all(all(v['identical'] for v in r['files'].values()) and r['canonical_identical'] and r['ledger_identical'] and all(x['status']=='Ok' for x in r['records'].values()) for r in rows)
(D/'preflight-comparison.json').write_text(json.dumps(dict(passed=passed,rows=rows,utc=time.time()),indent=2)+'\n')
assert passed,'preflight deterministic byte disagreement'
