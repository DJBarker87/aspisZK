from NMV_formal import *
for n,m in [(101,'NMV_SdkExec'),(102,'NMV_SnapshotExec'),(108,'NMV_CopyExec'),(109,'NMV_ConcreteWindows'),(106,'NMV_NoWrite241')]:
 a=f'NMV_L{n:03}'
 if (E/a/'receipt.json').exists():
  r=json.loads((E/a/'receipt.json').read_text());assert r['exit_status']==0
  assert sha((E/(m+'.lean')).read_bytes()) in r['source_hashes'].values()
  continue
 r=run(a,'lean',m)
 if r['exit_status']:raise SystemExit(r['exit_status'])
