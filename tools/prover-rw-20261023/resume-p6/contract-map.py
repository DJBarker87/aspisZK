"""Read-only exact spans and source-assessment; writes only a requested output."""
from pathlib import Path
import hashlib,json,sys
D=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
s=(D/'proof/selected.rs').read_bytes()
def span(a,b):
 start=s.index(a.encode());end=s.index(b.encode(),start) if b else len(s)
 return dict(byte_start=start,byte_end_exclusive=end,line_start=s[:start].count(b'\n')+1,line_end=s[:end].count(b'\n')+1,sha256=sha(s[start:end]),source=s[start:end].decode())
parts={
'carriers':span('struct ProverRwResumeP6Request','impl ProverRwResumeP6Request'),
'start':span('    fn start(','    // Native effect producer.'),
'draw':span('    // Native effect producer.','impl ProverRwResumeP6Draw'),
'resume':span('impl ProverRwResumeP6Draw','impl StateOnlyAttemptSecrets'),
'driver':span('impl StateOnlyAttemptSecrets',None)}
assert s==(D/'compact/proof/selected.rs').read_bytes()
E=D.parents[2]/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023'
# parents[2] = repository root, since D=tools/prover-rw-20261023/resume-p6.
old=E/'native-owned-drop/zeroize-1.8.1-index.crates.io-1949cf8c6b5b557f.rs.txt'
assert old.read_bytes()==(D/'zeroize-original.rs.txt').read_bytes()
new=dict(schema='ProverRwResumeP6-concrete-source-map-v1',source_sha256=sha(s),spans=parts,
 representation='getrandom::Error(NonZeroI32) on host x86_64 Linux; original zeroize carrier layout retained',
 reused_source_assessment=dict(path=str(old.relative_to(D.parents[2])),sha256=sha(old.read_bytes()),identical=True,scope='D204 unchanged zeroize leaf source only; no new identity gate or caller theorem'),
 statement_status='concrete prospective proof target; no native/P6/semantic-erasure theorem',print_axioms='N/A: read-only source association')
Path(sys.argv[1]).write_text(json.dumps(new,indent=2)+'\n')
print('PASS exact prospective spans and unchanged prior zeroize source association')
