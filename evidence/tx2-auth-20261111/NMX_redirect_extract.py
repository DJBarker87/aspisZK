from NMX_formal import *
env=json.loads((E/'NMX_R3_ENV.json').read_text())
r=run('NMX_E003','extract','NMX_lane_emitted',['python3','NMX_stage.py','--extract','--function','lane','--workspace',B+'/NMX_src','--out',B+'/NMX_lane_emitted','--opacity',B+'/NMX_REDIRECT_OPACITY.json'],{n:(E/n).read_text() for n in ['NMX_stage.py','NMX_STAGING_MANIFEST.json','NMX_REDIRECT_OPACITY.json']},env_extra=env)
sys.exit(r['exit_status'])
