"""Focused proof candidates only, one scope at a time; retain every failure."""
import pathlib,sys,json,subprocess,time,re
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume10';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
a=int(sys.argv[1]);limit=int(sys.argv[2]);names=sys.argv[3:];assert 40406<=a<=limit<=40496
results=[];bad=set()
for p in E.glob('receipt-*.json'):
 rec=json.load(open(p))
 for row in rec['modules']:
  if not row.get('accepted'):bad.add(row['module'])
for name in names:
 path=L/(name+'.lean');assert path.exists()
 deps=re.findall(r'^import\s+(\S+)',path.read_text(),re.M)
 blocked=sorted(set(deps)&bad)
 if blocked:results.append(dict(module=name,blocked=blocked,charged=False));continue
 if a>limit:break
 q=subprocess.run([sys.executable,str(R/'tools/pv-reach-20261027/resume10-chunks.py'),str(a),'R1Z.'+name],capture_output=True,text=True)
 print(q.stdout[-4000:]+q.stderr[-2000:],flush=True)
 if q.returncode==78:
  results.append(dict(module=name,attempt=a,refusal=True,charged=False));a+=1
  (E/'proof-queue.json').write_text(json.dumps(dict(next_id=a,results=results),indent=2)+'\n');sys.exit(78)
 p=E/f'receipt-{a}.json'
 if not p.exists():sys.exit(q.returncode or 2)
 rec=json.load(open(p));results.append(dict(module=name,attempt=a,accepted=rec['accepted']))
 if not rec['accepted']:bad.add('R1Z.'+name)
 a+=1
 (E/'proof-queue.json').write_text(json.dumps(dict(next_id=a,results=results),indent=2)+'\n')
 if a%10==0:
  subprocess.run(['git','add','--',str(E.relative_to(R))],check=True)
  subprocess.run(['git','commit','-m',f'Record focused client proof attempts through {a-1}'],check=True)
print('NEXT',a,flush=True)
