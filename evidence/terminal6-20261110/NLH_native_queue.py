"""Sequential native pairs; no automatic retry of a failed positive."""
from pathlib import Path
import json,subprocess,sys
p=Path(__file__).resolve().parent
base=json.loads((p/'NLH_K002.json').read_text())
shapes=[('NKR_term_semantic_native','NKR_semantic_child_state_cut'),('NKR_term_semantic_native','NKR_semantic_digest_args_cut'),('NKR_term_semantic_native','NKR_semantic_digest_state_cut'),('NKR_scalar_windows_native','NKR_scalar_field_window_cut'),('NKR_scalar_windows_native','NKR_scalar_tail_window_cut'),('NKR_term_semantic_native','NKR_semantic_order_cut'),('NKR_prefix_native','NKR_validation_prefix_cut'),('NKR_prefix_native','NKR_terminal_gather_cell_cut'),('NKR_horner_native','NKR_horner_step_cut'),('NKR_horner_native','NKR_horner_control_cut')]
start=int(sys.argv[1]);chosen=shapes[int(sys.argv[2]):int(sys.argv[3])]
for module,harness in chosen:
 for control in [False,True]:
  a=f'NLH_K{start:03}';start+=1
  x=json.loads(json.dumps(base));x['attempt']=a;x['module']=harness;x.pop('deps_fingerprint',None)
  x['command'][-1]=a+'.json';x['native_command'][x['native_command'].index('--harness')+1]='pool_v1::pair_forest_semantic_terminal::'+module+'::'+harness
  x['env']['RUSTFLAGS']=base['env']['RUSTFLAGS']+(' --cfg NKR_invert' if control else '')
  x['collect']=[z.replace('NLH_K002',a) for z in base['collect']]
  x['expected_time']='Optimized compile then '+('matched corrupt-argument/reply control (expected failure): ' if control else 'missing native same-state cut: ')+harness
  x['sources']=[z for z in base['sources'] if not z.endswith('.xz')]+['NLH_forward.patch','NLH_Forward_native.rs.txt','NLH_FORWARD_TRANSCRIPTION.json']
  (p/(a+'.json')).write_text(json.dumps(x))
  r=subprocess.run([sys.executable,str(p/'NLH_run.py'),a])
  receipt=p/a/'receipt.json'
  if not receipt.exists():raise SystemExit('Unresolved infrastructure/input failure; never resubmit')
  text=(p/a/'stdout.log').read_text()
  ok=(r.returncode==1 and 'VERIFICATION:- FAILED' in text) if control else (r.returncode==0 and 'VERIFICATION:- SUCCESSFUL' in text)
  print(json.dumps(dict(attempt=a,harness=harness,control=control,expected_verdict=ok)),flush=True)
  if not ok:raise SystemExit(1)
