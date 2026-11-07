from NMX_formal import *
r=subprocess.run([sys.executable,str(E/'NMX_217_word64_generate.py'),'--check']);assert r.returncode==0
env=json.loads((E/'NMX_R3_ENV.json').read_text());env['LEAN_PATH']=B+'/NMX_NDB_seed:'+B+'/NMX_NCV_seed:'+env['LEAN_PATH']
modules=['NMX_R3_ScalarShift','NMX_R3_RawWord64Defs']+['NMX_R3_RawWord64Byte'+str(k) for k in range(8)]+['NMX_R3_RawWord64']
for n,m in enumerate(modules,731):
 r=run('NMX_L'+str(n),'lean',m,env_extra=env)
 if r['exit_status']:raise RuntimeError('STOP failed predecessor '+m)
