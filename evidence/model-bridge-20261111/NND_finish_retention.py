from NND_formal import *
r=run('NND_L058','audit','selected-closure-retention',command=['python3','NND_retention.py','NND_L058'],extra={n:(E/n).read_text() for n in ['NND_retention.py','NND_CURRENT_MODULES.json']})
sys.exit(r['exit_status'])
