from NLA_formal import *
for a,m in [('NLA_L004','NLA_RootPrefix'),('NLA_L005','NLA_LaneStep'),('NLA_L006','NLA_DataPrefix')]:
 r=run(a,'lean',m)
 assert r['exit_status']==0
subprocess.run([sys.executable,str(E/'NLA_pda_stage.py')],check=True)
