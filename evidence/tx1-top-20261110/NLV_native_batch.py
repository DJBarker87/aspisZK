from pathlib import Path
import subprocess,sys,json,re
E=Path(__file__).resolve().parent
start=int(sys.argv[1]);items=sys.argv[2:]
for n,item in enumerate(items,start):
 mode,polarity=item.split(':');bad=polarity=='control';assert polarity in ['cut','control']
 a=f'NLV_K{n:03d}';h=f'verifier::candidate::NLV_native::{mode if mode.startswith("prepare_") else "parent_"+mode}_{polarity}'
 subprocess.run([sys.executable,str(E/'NLV_kconfig.py'),a,h],check=True)
 with (E/(a+'-client.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NLV_run.py'),a],stdout=f,stderr=subprocess.STDOUT)
 p=E/a/'stdout.log';out=p.read_text() if p.exists() else ''
 source=(E/'NLV_native.rs.txt').read_text();module='crates/aspis-r1-cost-probe/src/NLV_native.rs'
 pins=json.loads((E/(a+'/sources/NLV_SOURCE_PINS.json')).read_text()) if (E/(a+'/sources/NLV_SOURCE_PINS.json')).exists() else {}
 pinned=__import__('hashlib').sha256(source.encode()).hexdigest()==pins.get(module)
 neg_lines=[j+1 for j,line in enumerate(source.splitlines()) if 'assert!(!good,' in line]
 failed_at=re.search(r'File: "crates/aspis-r1-cost-probe/src/NLV_native.rs", line (\d+), in ([^\n]+)',out)
 matched_negative=pinned and failed_at is not None and int(failed_at[1]) in neg_lines and failed_at[2].strip() in ['verifier::candidate::NLV_native::prefix_check','verifier::candidate::NLV_native::prefix_window','verifier::candidate::NLV_native::check','verifier::candidate::NLV_native::small_window']

 timed='timed out' in out.lower() or 'timeout' in out.lower() and 'VERIFICATION:-' not in out
 good=(r.returncode==0 and 'VERIFICATION:- SUCCESSFUL' in out) if not bad else (r.returncode==1 and 'VERIFICATION:- FAILED' in out and matched_negative and re.search(r'\*\*\s+1 of \d+ failed',out) is not None and not timed)
 x=dict(attempt=a,harness=h,mode=mode,control=bad,expected_verdict=bool(good),timed_out=timed,classification='LOCAL CUT CANDIDATE ONLY; full physical native producer, child domains and source installation remain OPEN')
 with (E/'NLV_NATIVE_CLASSIFICATION.jsonl').open('a') as f:f.write(json.dumps(x)+'\n')
 print(a,h,'expected' if good else 'REVIEW',flush=True)
 if not good:raise SystemExit(1)
