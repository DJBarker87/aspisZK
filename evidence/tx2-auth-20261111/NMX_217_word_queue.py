from NMX_formal import *
env=json.loads((E/'NMX_R3_ENV.json').read_text());env['LEAN_PATH']=B+'/NMX_NDB_seed:'+B+'/NMX_NCV_seed:'+env['LEAN_PATH']
for n,m in enumerate(['NMX_R3_RawWord32Defs']+['NMX_R3_RawWord32Byte'+str(k) for k in range(4)]+['NMX_R3_RawWord32'],697):
 r=run('NMX_L'+str(n),'lean',m,env_extra=env)
 if r['exit_status']:raise RuntimeError('STOP failed predecessor '+m)
