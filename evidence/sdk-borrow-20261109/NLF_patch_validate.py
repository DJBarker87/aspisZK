from NLF_formal import *
files={n:(E/n).read_text() for n in ['NLF_patch_validate_host.py','NLF_native_packets.patch','NLF_PATCH_IDENTITY.json']}
r=run('NLF_L082','inspect','harness-patch-identity',['python3','NLF_patch_validate_host.py'],files)
assert r['exit_status']==0
r=ssh('cat '+B+'/NLF_PATCH_VALIDATION.json');assert r.returncode==0
(E/'NLF_PATCH_VALIDATION.json').write_text(r.stdout)
