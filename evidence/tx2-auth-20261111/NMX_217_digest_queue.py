from NMX_formal import *
env=json.loads((E/'NMX_R3_ENV.json').read_text());env['LEAN_PATH']=B+'/NMX_NDB_seed:'+B+'/NMX_NCV_seed:'+env['LEAN_PATH']
for n,m in enumerate(['NMX_R3_PrimaryWindow','NMX_R3_PrimaryDigestStep','NMX_R3_PrimaryDigestRun','NMX_R3_DigestWords','NMX_R3_DigestPositive','NMX_R3_DigestTotal'],708):
 r=run('NMX_L'+str(n),'lean',m,env_extra=env)
 if r['exit_status']:raise RuntimeError('STOP failed predecessor '+m)
