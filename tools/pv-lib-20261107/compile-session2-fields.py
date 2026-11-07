"""Focused graph compiles, serial, fresh IDs, commit each passing module."""
import json,pathlib,subprocess,sys,time
E=pathlib.Path('evidence/pv-lib-20261107')
queue=['PV_FN_THREAD_f124Consumer','PV_FN_THREAD_f124_Counts',
 'PV_LIB_Atomic121','PV_LIB_Arc124Allocated','PV_LIB_Arc124','PV_LIB_Arc124Counts',
 'PV_LIB_ArcClone360','PV_LIB_Box443','PV_LIB_Box537','PV_LIB_Box458','PV_LIB_Clone214',
 'PV_LIB_ThreadNamed','PV_LIB_NativeGraph','PV_LIB_SpawnNative','PV_LIB_ScopeNative','PV_LIB_TlsNative','PV_LIB_RootNative',
 'PV_LIB_SliceNativeGraph','PV_LIB_SliceAllocNative','PV_LIB_SliceLoopNative','PV_LIB_SliceBuiltinNative',
 'PV_LIB_SliceDrop','PV_LIB_SliceNoAlloc','PV_LIB_SliceAllocators','PV_LIB_SlicePtrParts',
 'PV_LIB_SliceAlloc59','PV_LIB_SliceAlloc47','PV_LIB_SliceAlloc48','PV_LIB_SliceCtor35']
for m in queue:
 p=pathlib.Path('lean',m+'.lean')
 receipts=[json.loads(q.read_text()) for q in E.glob('receipt-*.json')]
 if any(r['target']==m and r['accepted'] for r in receipts):continue
 if not p.exists():
  assert m.startswith('PV_FN_THREAD_')
  p.write_bytes(subprocess.check_output(['git','show','fc0340264851248e164a098c170cc53e22857085:lean/'+m+'.lean']))
 subprocess.run(['git','add','--sparse',str(p)],check=True)
 for retry in range(10):
  for q in E.glob('refusal-*.json'):
   delay=json.loads(q.read_text())['epoch']+181-time.time()
   while delay>0:
    print('COOLDOWN',round(delay),flush=True);time.sleep(min(60,delay));delay=json.loads(q.read_text())['epoch']+181-time.time()
  a=max(int(q.stem.split('-')[-1]) for q in E.glob('turn-*.json') if int(q.stem.split('-')[-1])<49480)+1
  assert 49326<=a<=49479
  print('FIELD',a,m,flush=True)
  rc=subprocess.run([sys.executable,'tools/pv-lib-20261107/compile.py',str(a),m]).returncode
  files=[str(q) for q in E.glob('*'+str(a)+'*')]
  subprocess.run(['git','add','--sparse',*files],check=True)
  if rc==78:
   subprocess.run(['git','commit','--only',*files,'-m','Record refused PLIB field '+str(a)],check=True);continue
  if rc:
   archive=E/'failed-sources'/(str(a)+'.lean.xz')
   import lzma
   archive.write_bytes(lzma.compress(p.read_bytes()))
   print('STOP',a,m,rc,flush=True);sys.exit(rc)
  subprocess.run(['git','commit','--only',str(p),*files,'-m','Add deterministic library field '+m],check=True)
  break
 else:sys.exit('ten admission refusals')
