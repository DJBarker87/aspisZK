from NMV_formal import *
name='TAS_Interfaces';src='NMV_generated/'+name+'.lean'
env=json.loads((E/'NMV_ENV.json').read_text())
r=run('NMV_L105','support',name,command=[env['LEAN_SYSROOT']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NMV_generated','-o','NMV_objects/'+name+'.olean',src],extra={src:(E.parent/'top-assembly-20261107'/(name+'.lean')).read_text()})
sys.exit(r['exit_status'])
