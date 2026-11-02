"""Read-only std1.94.1 stderr control association; primitive fidelity remains P."""
from pathlib import Path
import subprocess,shlex,json,hashlib,sys,re
E=Path('evidence/pv-evh10-20261102')
rows=json.load(open(E/'diagnostic-write-source.json'))
code='''from pathlib import Path
import json,hashlib,sys
rows=json.load(sys.stdin);out=[]
for r in rows:
 p=Path(r['path']);s=p.read_text();a=s.index(r['anchor']);i=s.index('{',a);j=i+1;n=1
 while n:
  n+=(s[j]=='{')-(s[j]=='}');j+=1
 out.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),anchor=r['anchor'],text=s[a:j]))
print(json.dumps(out))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(rows),text=True,capture_output=True);assert r.returncode==0,r.stderr
assert json.loads(r.stdout)==rows
b={r['anchor']:r['text'] for r in rows}
for t in ['while !buf.is_empty()', 'Ok(0)', 'Error::WRITE_ALL_EOF', 'buf = &buf[n..]', 'e.is_interrupted()', 'Err(e) => return Err(e)']:assert t in b['fn write_all(&mut self, mut buf: &[u8])']
assert 'self.lock().write_all(buf)' in b['impl Write for &Stderr {']
assert 'self.inner.borrow_mut().write_all(buf)' in b['impl Write for StderrLock']
assert 'handle_ebadf(self.0.write_all(buf), || Ok(()))' in b['impl Write for StderrRaw']
assert 'Err(ref e) if stdio::is_ebadf(e) => default()' in b['fn handle_ebadf']
assert 'ManuallyDrop::new(FileDesc::from_raw_fd(STDERR_FILENO)).write(buf)' in b['impl io::Write for Stderr']
mods=['ClientOverflow','LiteralWriteAll','StderrWrite'];laws=[]
for m in mods:
 p=Path('lean/PV_EVH_'+m+'.lean');raw=p.read_bytes();t=raw.decode();sha=hashlib.sha256(raw).hexdigest()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s',t,re.M)
 rs=[json.load(open(q)) for q in E.glob('receipt-*.json') if json.load(open(q)).get('accepted') and json.load(open(q)).get('target')=='PV_EVH_'+m]
 assert len(rs)==1 and rs[0]['source_sha256']==sha,(m,'unaccepted')
 laws.append(dict(module='PV_EVH_'+m,source_sha256=sha,attempt=rs[0]['attempt']))
out=dict(evidence_class='structural association of inspected std1.94.1 writer control to checked local models, not complete native diagnostics',sources=[{k:v for k,v in x.items() if k!='text'} for x in rows],laws=laws,
 control=['write_all empty/zero/partial/interrupted/error branches retain world and prefix','interrupted classification, error drop and WriteZero construction use the inherited stateful WriteAll.Driver','StderrRaw EBADF classification and error drop occur inside guard scope','ordinary error reaches caller after guard release; ignoreWrite then drops returned io::Error','no_success for capacity overflow; source-failure projections are explicitly retained'],
 retained=['actual libc/FileDesc write and signed return/errno association','ErrorKind/EBADF classification and full io::Error constructor/drop representation','stderr lock/RefCell acquire/release, reentrancy/borrow faults and scheduling','hook Box allocation, installation, environment/cache/backtrace disabled law and adopted abort profile','allocator metadata/ValidAnswer/RawVec/Global/System and exact actual WORLD selection','full extracted client/prover entry and callback installation; D520/U/D524 inputs','L3 joint observation and V370/V371'],trust_fields_added=[],rows_removed=[])
p=E/'diagnostic-writer-binding.json'
if '--check' in sys.argv:assert json.load(open(p))==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print('PASS inspected stderr control/checked local laws; primitive/guard/drop/native-entry fidelity remains OPEN')
