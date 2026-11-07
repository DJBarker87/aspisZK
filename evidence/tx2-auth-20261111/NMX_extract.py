from NMX_formal import *
r=run('NMX_E002','extract','NMX_auth_cut_emitted',['python3','NMX_stage.py','--extract','--function','auth','--workspace',B+'/NMX_src','--out',B+'/NMX_auth_cut_emitted','--opacity',B+'/NMX_OPACITY.json'],{n:(E/n).read_text() for n in ['NMX_stage.py','NMX_STAGING_MANIFEST.json','NMX_OPACITY.json']})
sys.exit(r['exit_status'])
