from NMW_formal import *
fn=sys.argv[1];assert fn in ['entry','process']
a='NMW_E001' if fn=='entry' else 'NMW_E002';out='NMW_'+fn+'_emitted'
command=['python3','NMW_stage.py','--extract','--function',fn,'--workspace',B+'/NMW_src','--out',B+'/'+out,'--opacity',B+'/NMW_OPACITY.json']
if fn=='process':command=['python3','NMW_extract_host.py']
files={n:(E/n).read_text() for n in ['NMW_stage.py','NMW_STAGING_MANIFEST.json','NMW_OPACITY.json']}
if fn=='process':
    import base64
    admission(a+'_transport')
    payload={n:base64.b64encode((E/n).read_bytes()).decode() for n in ['NMW_FROZEN_PAYLOAD.json.xz','NMW_FROZEN_PAYLOAD.json.sha256']}
    x=ssh('python3',f"from pathlib import Path\nimport json,base64\nb=Path({B!r})\nfor n,t in json.loads({json.dumps(payload)!r}).items():(b/n).write_bytes(base64.b64decode(t))")
    assert x.returncode==0,x.stderr
    for n in ['NMW_extract_host.py','NMW_POOL_AMENDMENT.json']:files[n]=(E/n).read_text()
r=run(a,'extract',out,command,files);sys.exit(r['exit_status'])
