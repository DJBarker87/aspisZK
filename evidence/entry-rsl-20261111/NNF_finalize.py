from NNF_formal import *
files={n:(E/n).read_text() for n in ['NNF_finalize_host.py','NNF_ENV.json','NNF_SEED_EXPECTED.json']}
r=run('NNF_L028','inspect','NNF_retention',['python3','NNF_finalize_host.py','NNF_L028'],files)
sys.exit(r['exit_status'])
