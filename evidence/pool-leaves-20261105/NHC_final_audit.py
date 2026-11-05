from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for i,mode in [(65,'batch0'),(66,'batch1'),(67,'scan')]:
 a=f'NHC_L{i:03}';r=subprocess.run([sys.executable,str(E/'NHC_run.py'),a,'audit',mode],capture_output=True,text=True);(E/(a+'-client.log')).write_text(r.stdout+r.stderr);print(a,mode,r.returncode,flush=True)
 if r.returncode:
  rc=json.loads((E/('NHC_audit/'+mode+'/proof'+mode[-1]+'.json')).read_text()) if mode.startswith('batch') else {}
  accepted=rc.get('results') and all(set(z['walked_axioms'])<={'Classical.choice','Quot.sound','propext'} and (z['equal'] or z['root']=='NHC_DecodeModel.decoder_error') for z in rc['results'])
  if not accepted:print((r.stdout+r.stderr)[-1000:]);sys.exit(r.returncode)
  print('Raw-standard summary disagreement accepted under binding ab-prime; original nonzero exit retained',flush=True)
