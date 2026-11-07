from NMV_formal import *
files={n:(E/n).read_text() for n in ['NMV_retention.py','NMV_EXPORT_MODULES.json','NMV_ENV.json','NMV_NNC_SEED.json']}
r=run('NMV_L128','inspect','resume_retention',['python3','NMV_retention.py'],files)
sys.exit(r['exit_status'])
