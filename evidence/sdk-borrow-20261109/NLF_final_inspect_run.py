from NLF_formal import *
files={n:(E/n).read_text() for n in ['NLF_FinalInspect.py','NLF_POOL_MANIFEST_IDENTITY.json','NLF_SDK_PINS.json']}
files['NLF_final_inspect_config.json']=json.dumps(dict(attempt='NLF_L073',root_package='aspis-r1-cost-probe-program'))
r=run('NLF_L073','inspect','SDK-source-and-lock-parity',['python3','NLF_FinalInspect.py','NLF_final_inspect_config.json'],files)
assert r['exit_status']==0
r=ssh('cat '+B+'/NLF_FINAL_SOURCE.json');assert r.returncode==0
(E/'NLF_FINAL_SOURCE.json').write_text(r.stdout)
