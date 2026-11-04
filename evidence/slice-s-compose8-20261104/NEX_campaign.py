"""Serial native cuts; stop on timeout/error rather than replay unchanged shapes."""
from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent;n=int(sys.argv[1]);family=sys.argv[2];slots=[None] if len(sys.argv)<4 else [int(s) for s in sys.argv[3].split(',')]
for slot in slots:
 for mode in (sys.argv[4].split(',') if len(sys.argv)>4 else ['positive','value','allocation','argument','reply']):
  if n>140:raise SystemExit('budget exhausted')
  a=f'NEX_K{n:03}';n+=1
  args=[sys.executable,str(E/'NEX_prepare_decoder.py'),family,mode]+([] if slot is None else [str(slot)])
  subprocess.run(args,check=True);(E/(a+'-shape.json')).write_bytes((E/'NEX_DECODER_CURRENT.json').read_bytes())
  parent='pair_forest_terminal' if family in ['common','lane'] else 'pair_tree_profile'
  r=subprocess.run([sys.executable,str(E/'NEX_kani_run.py'),a,'kani','pool_v1::'+parent+'::NEX_decoder::decoder'],capture_output=True,text=True)
  print(a,family,slot,mode,r.stdout[-1100:],r.stderr,flush=True)
  log=(E/a/'stdout.log').read_text()
  if 'VERIFICATION:- SUCCESSFUL' in log:
   if mode!='positive':raise SystemExit('finding: control unexpectedly passed')
  elif 'Failed Checks:' in log:
   if mode=='positive':raise SystemExit('positive counterexample requires diagnosis')
  else:raise SystemExit('excluded compile/timeout; inspect and split, no unchanged rerun')
