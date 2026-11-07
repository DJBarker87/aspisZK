from NMX_formal import *
env=json.loads((E/'NMX_R3_ENV.json').read_text())
r=run('NMX_E004','extract','NMX_registry_emitted',['python3','NMX_stage.py','--extract','--function','registry','--workspace',B+'/NMX_src','--out',B+'/NMX_registry_emitted','--opacity',B+'/NMX_REDIRECT_OPACITY.json'],{n:(E/n).read_text() for n in ['NMX_stage.py','NMX_STAGING_MANIFEST.json','NMX_REDIRECT_OPACITY.json']},env_extra=env)
sys.exit(r['exit_status'])
