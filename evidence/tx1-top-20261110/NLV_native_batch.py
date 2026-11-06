from pathlib import Path
import subprocess,sys,json,re
E=Path(__file__).resolve().parent
start=int(sys.argv[1]);items=sys.argv[2:]
for n,item in enumerate(items,start):
 mode,polarity=item.split(':');bad=polarity=='control';assert polarity in ['cut','control']
 a=f'NLV_K{n:03d}';h=f'verifier::candidate::NLV_native::parent_{mode}_{polarity}'
 subprocess.run([sys.executable,str(E/'NLV_kconfig.py'),a,h],check=True)
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NLV_run.py'),a],stdout=f,stderr=subprocess.STDOUT)
 p=E/a/'stdout.log';out=p.read_text() if p.exists() else ''
 timed='timed out' in out.lower() or 'timeout' in out.lower() and 'VERIFICATION:-' not in out
 good=(r.returncode==0 and 'VERIFICATION:- SUCCESSFUL' in out) if not bad else (r.returncode==1 and 'VERIFICATION:- FAILED' in out and 'NLV matched corruption' in out and re.search(r'\*\*\s+1 of \d+ failed',out) is not None and not timed)
 x=dict(attempt=a,harness=h,mode=mode,control=bad,expected_verdict=bool(good),timed_out=timed,classification='LOCAL CUT CANDIDATE ONLY; full physical native producer, child domains and source installation remain OPEN')
 with (E/'NLV_NATIVE_CLASSIFICATION.jsonl').open('a') as f:f.write(json.dumps(x)+'\n')
 print(a,h,'expected' if good else 'REVIEW',flush=True)
 if not good:raise SystemExit(1)
