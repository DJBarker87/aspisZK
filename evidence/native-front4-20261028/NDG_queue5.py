from pathlib import Path
import subprocess,os,json,sys
E=Path(__file__).resolve().parent
prefix='r1_pool_adapter::owned::NDG_owned::'
pairs=[(prefix+'length_custom_observation','cfg'),(prefix+'data_custom_observation','cfg'),(prefix+'data_success_contract','data'),('NDG_kmx::KMX_to_vec_correct','kmx'),(prefix+'zero_window','cfg'),(prefix+'zero_empty','cfg'),(prefix+'zero_reject','cfg'),(prefix+'snapshot_one','cfg'),(prefix+'snapshot_wrong_length','cfg'),(prefix+'snapshot_borrow_error','cfg'),('r1_pool_adapter::NDG_native::lane_wrong_length','cfg'),('r1_pool_adapter::NDG_native::scan_wrong_length','cfg'),(prefix+'data_empty_observation','cfg')]
for i,(target,mode) in enumerate(pairs):
 for neg in [False,True]:
  n=25+2*i+int(neg);a=f'NDG_K{n:03}';env=dict(os.environ);h=target
  if neg:
   if mode=='cfg':env['NDG_RUST_CFG']='NDG_negative'
   elif mode=='kmx':h='NDG_kmx::KMX_to_vec_wrong'
   else:env['NDG_INVERT']=mode
  r=subprocess.run([sys.executable,str(E/'NDG_run.py'),a,'kani',h],env=env,capture_output=True,text=True)
  (E/(a+'-queue.log')).write_text(r.stdout+r.stderr)
  assert r.returncode==0,(a,r.stdout+r.stderr)
  rc=json.loads((E/a/'receipt.json').read_text());print(a,h,rc['exit_status'],flush=True)
  # Every next positive is an independent body/domain. Negative changes the assertion;
  # never repeat a timed-out positive. Preserve all timeout/failure evidence.
