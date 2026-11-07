from NND_formal import *
r=run('NND_E002','extraction','zero',['python3','NND_stage.py','--extract','--function','zero','--workspace',B+'/NND_workspace','--out',B+'/NND_zero'],extra={n:(E/n).read_text()for n in ['NND_stage.py','NND_OPACITY.json']})
raise SystemExit(r['exit_status'])
