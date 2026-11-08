"""Serial focused PLIB launch using the existing pinned run2/NEP runners."""
import hashlib,json,lzma,pathlib,shlex,subprocess,sys,time
E=pathlib.Path('evidence/pv-lib-20261107/lane-A');H='/home/dombarker/project-offloads/codex-pv-lib-20261107/lane-A'
host='dombarker@100.108.41.90'
a=int(sys.argv[1]);m=sys.argv[2];audit=sys.argv[3:]==['--audit']
assert ((49482<=a<=49499 or 49890<=a<=49899)) if audit else (49458<=a<=49479 or 49800<=a<=49889)
for q in E.glob('refusal-*.json'):
    assert time.time()-json.loads(q.read_text())['epoch']>=180
p=pathlib.Path(sys.argv[3]) if len(sys.argv)>3 and not audit else pathlib.Path('lean',m+'.lean');raw=p.read_text()
assert subprocess.check_output(['git','show',':'+str(p)],text=True)==raw,'stage exact input first'
turn_cmd=['ssh',host,'STREAMB_SLOTS=3 /home/dombarker/streamb-slots/turn.sh']
t0=time.time();turn=subprocess.run(turn_cmd,text=True,capture_output=True)
t=dict(command=turn_cmd,attempt=a,exit=turn.returncode,wall=time.time()-t0,stdout=turn.stdout,stderr=turn.stderr)
(E/f'turn-{a}.json').write_text(json.dumps(t,indent=2)+'\n')
assert turn.returncode==0,t
x=dict(attempt=a,module=m,source=raw,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
       source_path=str(p),source_index_blob=subprocess.check_output(['git','rev-parse',':'+str(p)],text=True).strip(),audit=audit,turn=t)
if audit:
    x['audit_wrapper']=pathlib.Path('tools/pv-lib-20261107/run-thread-audit.py').read_text()
    manifest='AUDIT_ROOTS.json'
    x['runtime_modules']=json.loads((E/manifest).read_text())['modules']
code=(E/'focused-host.py').read_text()
q=subprocess.run(['ssh',host,'python3 -c '+shlex.quote(code)],input=json.dumps(x),text=True,capture_output=True)
(E/f'transport-{a}.json').write_text(json.dumps(dict(exit=q.returncode,stdout=q.stdout,stderr=q.stderr),indent=2)+'\n')
print(q.stdout);print(q.stderr,file=sys.stderr)
for kind,suffix in [('id-audit','json'),('submission','json'),('admission','json'),('receipt','json'),('refusal','json'),('resolution','json'),('out','log'),('time','log')]:
    r=subprocess.run(['ssh',host,f'cat {H}/evidence/{kind}-{a}.{suffix}'],text=True,capture_output=True)
    if r.returncode==0:
        out=E/f'{kind}-{a}.{suffix}'
        if kind=='resolution':out.with_suffix('.json.xz').write_bytes(lzma.compress(r.stdout.encode()))
        else:out.write_text(r.stdout)
sys.exit(q.returncode)
