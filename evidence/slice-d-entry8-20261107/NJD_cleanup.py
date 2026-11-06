from NJD_formal import *
r=run('NJD_L032','inspect','NJD_cleanup',['python3','NJD_cleanup_host.py'],{'NJD_cleanup_host.py':(E/'NJD_cleanup_host.py').read_text()});assert r['exit_status']==0
r=ssh('cat '+B+'/NJD_HOST_END.json');assert r.returncode==0;(E/'NJD_HOST_END.json').write_text(r.stdout)
