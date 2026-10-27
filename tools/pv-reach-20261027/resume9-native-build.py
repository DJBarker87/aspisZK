"""Compile exact native-interface prerequisites, one charged attempt per module.
No chunk waiver is inferred for this additional closure. Failed committed
sources remain unchanged; only independent available work continues.
"""
import pathlib,json,subprocess,sys,time
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume9'
a=int(sys.argv[1]);limit=int(sys.argv[2]);assert 40210<=a<=limit<=40296
rows=json.load(open(E/'native-project-closure.json'));mapping={r['module']:r for r in rows};old={r['module'] for r in json.load(open(E/'project-closure.json'))}
available=set(old);attempted=set();progress=[]
for p in E.glob('receipt-[0-9]*.json'):
 x=json.loads(p.read_text())
 for r in x['modules']:
  if r.get('exit') is not None and r['module'] in mapping:
   attempted.add(r['module'])
   if r.get('accepted'):available.add(r['module'])
# Compose the smallest exact native input first, then the actual false/true
# smaller fixture carriers before the larger association-type import chain.
order=[]
def visit(m):
 if m in order or m not in mapping:return
 for d in mapping[m]['imports']:visit(d)
 order.append(m)
for root in ['R1Z.PV_Src_NativeInput','R1Z.PV_Src_FrozenFixtures','R1Z.PV_Src_PublicDeploymentAssociation','R1Z.PV_Src_ExternalAssociation','R1Z.PV_Src_RecordAssociation']:visit(root)
for m in order:
 if a>limit:break
 if m in available or m in attempted:continue
 missing=[d for d in mapping[m]['imports'] if d in mapping and d not in available]
 if missing:progress.append(dict(module=m,blocked=missing));continue
 while a<=limit:
  q=subprocess.run([sys.executable,str(R/'tools/pv-reach-20261027/resume9-chunks.py'),str(a),m,'--native'],capture_output=True,text=True)
  print(q.stdout[-1800:]+q.stderr[-500:],flush=True)
  p=E/f'receipt-{a}.json'
  if q.returncode==78:
   progress.append(dict(module=m,attempt=a,refusal=True,charged=False));a+=1
   (E/'native-progress.json').write_text(json.dumps(dict(next_id=a,steps=progress),indent=2)+'\n')
   time.sleep(180);continue
  if not p.exists():sys.exit(q.returncode or 2)
  rec=json.loads(p.read_text());progress.append(dict(module=m,attempt=a,accepted=rec['accepted']))
  if rec['accepted']:available.add(m)
  else:
   out=rec['modules'][-1].get('output','');print(out[-2500:],flush=True)
   if rec['modules'][-1].get('exit') is None:sys.exit(2)
  a+=1
  (E/'native-progress.json').write_text(json.dumps(dict(next_id=a,steps=progress,available_native=sorted(available-old)),indent=2)+'\n')
  if (a-40210)%10==0:
   files=[str(p.relative_to(R)) for p in E.glob('*') if p.is_file() and (any(str(i) in p.name for i in range(a-10,a)) or p.name=='native-progress.json')]
   subprocess.run(['git','add','--']+files,check=True,cwd=R)
   subprocess.run(['git','commit','-m',f'Record native boundary prerequisite attempts through {a-1}'],check=True,cwd=R)
  break
print('NEXT',a,flush=True)
