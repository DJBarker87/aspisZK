from NIV_formal import *
files={n:(E/n).read_text() for n in ['NIV_stage.py','NIV_extract_preflight_host.py','NIV_OPACITY.json']}
r=run('NIV_L021','preflight','entry_extraction_preflight',['python3','NIV_extract_preflight_host.py'],files,{'CARGO_TARGET_DIR':B+'/NIV_NHR_target','CARGO_NET_OFFLINE':'true','RUSTFLAGS':''});assert r['exit_status']==0
r=ssh('cat '+B+'/NIV_EXTRACTION_PREFLIGHT.json');assert r.returncode==0;(E/'NIV_EXTRACTION_PREFLIGHT.json').write_text(r.stdout)
print('PASS_BINDING_EXTRACTION_PREFLIGHT',flush=True)
