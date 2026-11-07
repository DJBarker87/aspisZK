from NMX_formal import *
s='''import LIBB_PoolLib
set_option autoImplicit false
#print RSL.OwnedAccount.data
#print RSL.TX2_234.immutableBranch
#print RSL.TX2_234.v1Branch
#check NND_Carrier.getter
'''
env=json.loads((E.parent/'libb-20261111/LIBB_L344/receipt.json').read_text())['env']
# Diagnostic only: inspect the supplying library's own retained owner selection.
r=run('NMX_L958','inspect','NMX_R3_SupplierShape',command=[env['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NMX_generated','NMX_generated/NMX_R3_SupplierShape.lean'],extra={'NMX_generated/NMX_R3_SupplierShape.lean':s},env_extra=env)
assert r['exit_status']==0
