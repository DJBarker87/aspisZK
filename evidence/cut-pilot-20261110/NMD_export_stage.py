from NMD_formal import *
r=run('NMD_L017','inspect','pin-final-closure-and-export',['python3','NMD_export.py'],{'NMD_export.py':(E/'NMD_export.py').read_text()});assert r['exit_status']==0
