"""Read detached progress; never launches or resumes any computation."""
import pathlib,json,subprocess,shlex,sys
E=pathlib.Path(__file__).parent;a=int(sys.argv[1]);V='/home/dombarker/project-offloads/codex-pv-lib-slice-20261107/v1-coherence'
code=r'''
import pathlib,json,subprocess
E=pathlib.Path('HOST')/'evidence';a=ATTEMPT;p=E/f'out-{a}.log';b=[]
if p.exists():
 for l in p.read_text().splitlines():
  if l.startswith('{"batch"'):b.append(json.loads(l))
s=dict(attempt=a,completed_batches=len(b),completed_roots=sum(x['root_count'] for x in b),all_completed_pass=all(x['accepted'] for x in b),last=b[-1] if b else None)
r=E/f'receipt-{a}.json'
if r.exists():
 q=json.load(open(r));s['receipt']={k:q[k] for k in ['exit','accepted','wall','peak_rss_kbytes','swaps','source_revision','tools_revision'] if k in q}
else:
 s['scope_properties']=subprocess.check_output(['systemctl','--user','show',f'pv-lib-{a}.scope','-p','ActiveState','-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','TasksMax'],text=True)
print(json.dumps(s))
'''.replace('HOST',V).replace('ATTEMPT',str(a))
r=subprocess.run(['ssh','-o','ConnectTimeout=10','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,text=True);assert r.returncode==0,r.stderr
s=json.loads(r.stdout)
if 'scope_properties' in s and not (E/f'LIVE_CAPS-{a}.json').exists():(E/f'LIVE_CAPS-{a}.json').write_text(json.dumps(dict(attempt=a,scope_properties=s['scope_properties']),indent=2)+'\n')
(E/f'PROGRESS-{a}.json').write_text(json.dumps(s,indent=2)+'\n');print(json.dumps(s))
