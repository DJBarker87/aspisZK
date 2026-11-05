from pathlib import Path
import subprocess,os,time
E=Path(__file__).resolve().parent
while not (E/'NGW_L061/receipt.json').exists():time.sleep(2)
def prep(n):subprocess.run(['python3',str(E/n)],check=True)
def run(a,h,invert=False,flag='NGW_invert'):
 env=dict(os.environ)
 if invert:env.update(NGW_INVERT='1',NGW_NATIVE_CFG=flag)
 with (E/(a+'-queue.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGW_run.py'),a,'kani',h],env=env,stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 p=E/a/'stdout.log'
 if not p.exists():raise SystemExit('missing receipt')
 if 'timed out' in p.read_text().lower():raise SystemExit('isolate timeout')
 if r.returncode!=(1 if invert else 0):raise SystemExit('isolate unexpected result')
prep('NGW_split_box_control.py')
run('NGW_K089','weights::NGW_new::box_g1',True)
prep('NGW_prepare_prefix.py')
for i in range(2):
 for inv in [False,True]:run(f'NGW_K{90+2*i+int(inv):03d}',f'weights::NGW_new::prefix_g{i}',inv)
for i,g in enumerate([1,2]):
 for inv in [False,True]:run(f'NGW_K{94+2*i+int(inv):03d}',f'verifier::NGM_helpers::round_g{g}',inv,'NGM_invert')
prep('NGW_prepare_abi.py')
for a,inv in [('NGW_K098',False),('NGW_K099',True)]:run(a,'fast_pairing::NGW_abi::nine_word_model',inv)
prep('NGW_prepare_round.py')
run('NGW_K100','verifier::NGW_round::round_frame')
