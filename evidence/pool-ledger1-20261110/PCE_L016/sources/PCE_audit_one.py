from pathlib import Path
import sys,subprocess,hashlib,json
B=Path.cwd();mode=sys.argv[1];p=B/'PCE_native/PCE_AuditDriver';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();before=sha(p)
allroots=json.loads((B/'PCE_ROOTS_ALL.json').read_text())['roots'];groups=json.loads((B/'PCE_GROUPS.json').read_text())
if mode.startswith('roots'):
 expected=groups[int(mode[5:])];(B/'PCE_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=expected)));arg='proof'
else:
 expected=[];arg=mode
 (B/'PCE_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=allroots)))
r=subprocess.run([str(p),arg],capture_output=True,text=True);print(r.stdout,end='');print(r.stderr,end='',file=sys.stderr)
results=[json.loads(l[11:]) for l in r.stdout.splitlines() if l.startswith('NEP_RESULT ')]
std={'propext','Classical.choice','Quot.sound'}
if mode.startswith('roots'):
 assert [x['root'] for x in results]==expected,('missing/raw roots',mode)
 assert all(set(x['walked_axioms'])<=std for x in results),'nonstandard raw axiom'
 # Ruling (ab')(3): raw ax2 walk is authoritative; retain every collector disagreement.
 assert r.returncode in [0,1] and all(x.get('root') for x in results)
 accepted=True
elif mode=='fixtures':
 assert r.returncode==0 and len(results)==8
 assert all(x['equal'] and len(x['walked_axioms'])==(1 if i<4 else 0) for i,x in enumerate(results));accepted=True
else:accepted=r.returncode==0
assert before==sha(p)
(B/('PCE_binary_'+mode+'.json')).write_text(json.dumps(dict(binary=str(p),sha256=before,unchanged=True,binary_exit=r.returncode,policy_exit=0 if accepted else r.returncode,results=results)))
sys.exit(0 if accepted else r.returncode)
