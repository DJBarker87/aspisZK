"""Compile unchanged canonical specifications privately, one admitted scope each."""
from NMV_formal import *
R=E.parent/'rowspec-lead-20261107'
order=['RSL_Base','RSL_Pool','RSL_Verifier','RSL_TX1_136','RSL_TX1_137','RSL_TX1_087','RSL_TX1_094','RSL_TX1_328','RSL_TX1_345','RSL_TX2_217','RSL_TX2_234','RSL_TX2_233','RSL_TX2_242','RSL_TX2_241','RSL_TX2_240','RSL_TX2_221','RSL_TX1_344','RSL_TX1_333','RSL_TX2_213','RSL_TX1_330']
if __name__=='__main__':
 for i,name in enumerate(order,23):
  a=f'NMV_L{i:03}'
  if (E/a/'receipt.json').exists():
   assert json.loads((E/a/'receipt.json').read_text())['exit_status']==0
   continue
  src='NMV_generated/'+name+'.lean'
  env=json.loads((E/'NMV_ENV.json').read_text())
  rc=run(a,'support',name,command=[env['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NMV_generated','-o','NMV_objects/'+name+'.olean',src],extra={src:(R/(name+'.lean')).read_text()})
  if rc['exit_status']:raise SystemExit(rc['exit_status'])
