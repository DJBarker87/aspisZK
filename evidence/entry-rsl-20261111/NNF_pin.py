from NNF_formal import *
for i in range(3):
 files={n:(E/n).read_text() for n in ['NNF_pin_host.py','NNF_ENV.json','NNF_PREDECESSOR_PIN.json']}
 r=run('NNF_L'+str(23+i).zfill(3),'inspect','NNF_pin_batch'+str(i),['python3','NNF_pin_host.py',str(i)],files)
 if r['exit_status']:sys.exit(r['exit_status'])
