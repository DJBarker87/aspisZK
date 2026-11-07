from NNC_formal import *
env=json.loads((E/'NNC_ENV.json').read_text());T=env['LEAN_SYSROOT'];src='NNC_generated/NNC_ImportClosure.lean'
r=run('NNC_L065','inspect','NNC_ImportClosure',[T+'/bin/lake','env','lean','-j1','-M7000','--run',src],{src:(E/'NNC_ImportClosure.lean').read_text()})
sys.exit(r['exit_status'])
