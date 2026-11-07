"""Compile unchanged merged interface inputs privately, with normal receipts."""
from NNE_formal import *
mods=[('NNE_L060','TCK_WeakRoot0','evidence/top-check-20261107/'),('NNE_L061','TAS_Interfaces','evidence/top-assembly-20261107/')]
for a,m,root in mods:
 src='NNE_deps/'+m+'.lean'
 body=Path(root+m+'.lean').read_text()
 env=json.loads((E/'NNE_ENV.json').read_text())
 cmd=[env['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-o','NNE_objects/'+m+'.olean',src]
 rc=run(a,'lean',m,command=cmd,extra={src:body})
 if rc['exit_status']:break
