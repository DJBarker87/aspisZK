from NLA_formal import *
for a,m in [('NLA_L007','NLA_DataPrefix'),('NLA_L008','NLA_OwnedData')]:
 r=run(a,'lean',m)
 assert r['exit_status']==0
subprocess.run([sys.executable,str(E/'NLA_pda_stage.py')],check=True)
