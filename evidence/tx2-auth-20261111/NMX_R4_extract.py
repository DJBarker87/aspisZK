from NMX_formal import *
r=run('NMX_E008','extract','NMX_auth_box_emitted',
 ['python3','NMX_R4_stage.py','--extract','--function','auth','--workspace',B+'/NMX_registry_r5_src',
  '--out',B+'/NMX_auth_box_emitted','--opacity',B+'/NMX_R4_OPACITY.json'],
 {n:(E/n).read_text() for n in ['NMX_R4_stage.py','NMX_STAGING_MANIFEST.json','NMX_R4_OPACITY.json']})
assert r['exit_status']==0
