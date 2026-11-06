from NJN_formal import *
r=run('NJN_L031','inspect','NJN_cleanup',['python3','NJN_cleanup_host.py'],{'NJN_cleanup_host.py':(E/'NJN_cleanup_host.py').read_text()});assert r['exit_status']==0
r=ssh('cat '+B+'/NJN_HOST_END.json');assert r.returncode==0,r.stderr
(E/'NJN_HOST_END.json').write_text(r.stdout)
