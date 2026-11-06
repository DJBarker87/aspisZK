from NJH_formal import *
r=run('NJH_L028','inspect','NJH_cleanup',['python3','NJH_cleanup_host.py'],{'NJH_cleanup_host.py':(E/'NJH_cleanup_host.py').read_text()});assert r['exit_status']==0
r=ssh('cat '+B+'/NJH_HOST_END.json');assert r.returncode==0;(E/'NJH_HOST_END.json').write_text(r.stdout)
print('Owned target/native rebuildables removed; cache and keys retained')
