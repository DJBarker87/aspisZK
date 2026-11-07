from NNC_formal import *
s=Path('evidence/top-check-20261107/TCK_WeakRoot0.lean').read_text()
env=json.loads((E/'NNC_ENV.json').read_text());t=env['LEAN_SYSROOT']
cmd=[t+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-R','NNC_dependencies','-o','NNC_objects/TCK_WeakRoot0.olean','NNC_dependencies/TCK_WeakRoot0.lean']
r=run('NNC_L014','inspect','TCK_WeakRoot0',cmd,{'NNC_dependencies/TCK_WeakRoot0.lean':s})
sys.exit(r['exit_status'])
