from NIV_formal import *
for i,m in [(10,'NIV_FrameWindows'),(11,'NIV_SnapshotWrite'),(12,'NIV_SnapshotDomain'),(13,'NIV_Inspect'),(14,'NIV_SdkFields')]:
 r=run('NIV_L%03d'%i,'lean',m)
 if r['exit_status']:sys.exit(r['exit_status'])
for phase in ['owner','meta']:
 subprocess.run([sys.executable,str(E/'NIV_make_sdk.py'),phase],check=True)
 r=subprocess.run([sys.executable,str(E/'NIV_packet_queue.py'),'sdk'])
 if r.returncode:sys.exit(r.returncode)
print('PASS_MODEL_AND_THREE_FIELD_CLASSES',flush=True)
