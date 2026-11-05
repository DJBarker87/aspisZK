"""Final source/configuration pairs with a concrete corrupted reply control."""
from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
jobs=[]
for k in range(1,8):
 for invert in [False,True]:jobs.append((27+2*(k-1)+int(invert),True,invert,f'transcript::NGQ_pairs::NGQ_pair{k}'))
for j,(verifier,target) in enumerate([(False,'r0_transcript::NGQ_harness::NGQ_query_words'),(False,'r0_transcript::NGQ_harness::NGQ_word_step'),(False,'r0_transcript::NGQ_harness::NGQ_outer_step_check'),(False,'r0_transcript::NGQ_harness::NGQ_default'),(True,'transcript::NGQ_tail::NGQ_tail'),(True,'transcript::NGQ_absorb::NGQ_absorb'),(True,'transcript::NGQ_init::NGQ_init')]):
 for invert in [False,True]:jobs.append((41+2*j+int(invert),verifier,invert,target))
for j,(verifier,target) in enumerate([(True,'transcript::NGQ_call::NGQ_decode_call'),(False,'r0_transcript::NGQ_iterator::NGQ_range_next')]):
 for invert in [False,True]:jobs.append((55+2*j+int(invert),verifier,invert,target))
jobs=[(num+1 if num>=35 else num,v,i,t) for num,v,i,t in jobs]
jobs=[(num,v,False,'r0_transcript::NGQ_harness::NGQ_word_branch_check') if num==45 else (num,v,i,t) for num,v,i,t in jobs]
jobs.append((60,False,True,'r0_transcript::NGQ_harness::NGQ_word_branch_check'))
for num,verifier,invert,target in jobs:
 a=f'NGQ_K{num:03}';env=dict(os.environ)
 if verifier:env['NGQ_VERIFIER']='1'
 if invert:env['NGQ_INVERT']='1'
 if (E/a/'receipt.json').exists():continue
 r=subprocess.run(['python3',str(E/'NGQ_run.py'),a,'kani',target],env=env,capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 p=E/a/'receipt.json'
 if not p.exists():raise SystemExit(a+' NO RECEIPT; STOP')
 rc=json.loads(p.read_text());raw=(E/a/'stdout.log').read_text()
 verdict='OTHER' if any(x in raw for x in ['CBMC timed out','CBMC failed','unwinding assertion']) else 'SUCCESSFUL' if 'VERIFICATION:- SUCCESSFUL' in raw else 'FAILED' if 'VERIFICATION:- FAILED' in raw else 'OTHER'
 print(a,target,verdict,rc['wall_seconds'],rc['peak_rss_kib'],flush=True)
 if verdict!=('FAILED' if invert else 'SUCCESSFUL'):raise SystemExit('STOP unexpected verdict; isolate/split before retry')
