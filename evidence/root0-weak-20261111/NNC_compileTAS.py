from NNC_formal import *
s=Path('evidence/top-assembly-20261107/TAS_Interfaces.lean').read_text()
env=json.loads((E/'NNC_ENV.json').read_text());t=env['LEAN_SYSROOT']
cmd=[t+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NNC_dependencies','-o','NNC_objects/TAS_Interfaces.olean','NNC_dependencies/TAS_Interfaces.lean']
r=run('NNC_L015','inspect','TAS_Interfaces',cmd,{'NNC_dependencies/TAS_Interfaces.lean':s})
sys.exit(r['exit_status'])
