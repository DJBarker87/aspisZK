import pathlib,subprocess,json,sys,time
E=pathlib.Path('evidence/pv-lib-20261107/lane-SLICE')
plan=json.loads(subprocess.check_output(['git','show','5e397cb3878:evidence/pv-lib-20261107/SESSION2_SLICE_REPLAY_ORDER.json']))
queue=plan['modules'][27:-4]
for m,size in queue:
 receipts=[json.loads(p.read_text()) for p in E.glob('receipt-*.json')]
 if any(r['target']==m and r['accepted'] for r in receipts):continue
 for retry in range(10):
  ids=[int(p.stem.split('-')[-1]) for p in E.glob('turn-*.json')]
  a=max(ids,default=49599)+1
  if a>49680:sys.exit('reserve nine Lean IDs for graphs and audit driver')
  print('REPLAY',a,m,flush=True)
  rc=subprocess.run([sys.executable,str(E/'compile.py'),str(a),m,'--provider'],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
  print(rc.stdout[-1000:],flush=True)
  files=[str(p) for p in E.glob('*'+str(a)+'*')]
  if rc.returncode not in (0,78):sys.exit('stopped '+m)
  h=E/'HANDOFF.md';h.write_text(h.read_text()+f'\nAttempt {a}: {m}, '+('passed pinned focused replay.' if rc.returncode==0 else 'refused; ID spent.')+'\n')
  subprocess.run(['git','add','--sparse',str(E)],check=True,stdout=subprocess.DEVNULL)
  subprocess.run(['git','commit','-m',('Replay pinned SLICE provider ' if rc.returncode==0 else 'Record refused SLICE replay ')+m],check=True,stdout=subprocess.DEVNULL)
  if rc.returncode==0:break
  for _ in range(3):time.sleep(60)
 else:sys.exit('ten refusals')
