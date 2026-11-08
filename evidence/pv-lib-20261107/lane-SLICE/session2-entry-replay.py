import pathlib,json,subprocess,sys,time
E=pathlib.Path('evidence/pv-lib-20261107/lane-SLICE')
p=json.loads((E/'SESSION2_ENTRY_PLAN.json').read_text())
ids=iter(range(49913,49999))
for m in p['modules']:
 for a in ids:
  if (E/f'turn-{a}.json').exists():continue
  print('REPLAY',a,m,flush=True)
  r=subprocess.run([sys.executable,str(E/'compile.py'),str(a),m,'--provider','--revision',p['revision']],capture_output=True,text=True)
  print(r.stdout[-1800:],r.stderr[-1000:],flush=True)
  if r.returncode not in (0,78):sys.exit(r.returncode)
  h=E/'HANDOFF.md';h.write_text(h.read_text()+f'\nD978 attempt {a}: {m}: '+('passing pinned replay.' if r.returncode==0 else 'admission refused, ID spent.')+'\n')
  subprocess.run(['git','add','--sparse',str(E)],check=True)
  subprocess.run(['git','commit','-m',f'Replay SLICE Foundation entry provider {m}' if r.returncode==0 else f'Record SLICE admission refusal {a}'],check=True)
  if r.returncode==0:break
  for _ in range(3):time.sleep(60)
 else:sys.exit('ID block exhausted')
