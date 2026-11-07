"""One focused compile at a time; commit each passing module immediately."""
import pathlib,subprocess,json,sys,time,lzma
E=pathlib.Path('evidence/pv-lib-20261107/lane-SLICE')
def launch(m,provider=False,revision=None):
 for retry in range(10):
  ids=[int(p.stem.split('-')[-1]) for p in E.glob('turn-*.json') if int(p.stem.split('-')[-1])<49690]
  a=max(ids,default=49599)+1
  if a>49689:sys.exit('authorized Lean block exhausted')
  p=pathlib.Path('lean',m+'.lean')
  if not provider:subprocess.run(['git','add','--sparse',str(p)],check=True)
  cmd=[sys.executable,str(E/'compile.py'),str(a),m]
  if provider:cmd+=['--provider','--revision',revision]
  print('FOCUSED',a,m,flush=True)
  r=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
  print(r.stdout[-3500:],flush=True)
  h=E/'HANDOFF.md';h.write_text(h.read_text()+f'\nAttempt {a}: {m}, exit{r.returncode}.\n')
  if r.returncode not in (0,78):
   (E/'failed-sources').mkdir(exist_ok=True)
   raw=subprocess.check_output(['git','show',revision+':'+str(p)]) if provider else p.read_bytes()
   (E/'failed-sources'/f'{a}.lean.xz').write_bytes(lzma.compress(raw))
   if not provider:subprocess.run(['git','restore','--staged',str(p)],check=True)
   subprocess.run(['git','add','--sparse',str(E)],check=True)
   subprocess.run(['git','commit','-m','Record failed SLICE focused proof '+m],check=True,stdout=subprocess.DEVNULL)
   sys.exit('changed proof or environment review required for '+m)
  subprocess.run(['git','add','--sparse',str(E)],check=True)
  if r.returncode==78 and not provider:subprocess.run(['git','restore','--staged',str(p)],check=True)
  subprocess.run(['git','commit','-m',('Replay pinned SLICE provider ' if provider else 'Certify SLICE library adapter ')+m if r.returncode==0 else 'Record refused SLICE attempt '+str(a)],check=True,stdout=subprocess.DEVNULL)
  if r.returncode==0:return
  for _ in range(3):time.sleep(60)
 sys.exit('ten refusals')
for m in ['PV_LIB_SLICE_BoundedRun','PV_LIB_SLICE_F32','PV_LIB_SLICE_F33','PV_LIB_SLICE_TypedDrop']:
 if not any(json.loads(p.read_text()).get('target')==m and json.loads(p.read_text()).get('accepted') for p in E.glob('receipt-*.json')):launch(m)
entry=json.loads((E/'ENTRY_PREFLIGHT.json').read_text())
for m in entry['missing_modules'][:5]:
 if not any(json.loads(p.read_text()).get('target')==m and json.loads(p.read_text()).get('accepted') for p in E.glob('receipt-*.json')):launch(m,True,entry['revision'])
for m in ['PV_LIB_SLICE_EntryReference','PV_LIB_SLICE_RawAudit']:
 if not any(json.loads(p.read_text()).get('target')==m and json.loads(p.read_text()).get('accepted') for p in E.glob('receipt-*.json')):launch(m)
