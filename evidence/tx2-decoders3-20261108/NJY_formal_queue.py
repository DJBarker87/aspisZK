from NJY_formal import *
for a,m in [('NJY_L002','NJY_Checkpoint'),('NJY_L003','NJY_Master'),('NJY_L004','NJY_Entry'),('NJY_L005','NJY_Registry')]:
 r=run(a,'lean',m);assert r['exit_status']==0
subprocess.run([sys.executable,str(E/'NJY_next_queue.py')],check=True)
