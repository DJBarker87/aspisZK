"""Check the explicit native iteration projection against immutable frozen bytes."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
E=Path(__file__).resolve().parent;F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';P='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'
s=subprocess.check_output(['git','show',F+':'+P],text=True)
a=s.index('            if accounts[previous].key() == accounts[index].key() {');b=s.index('            previous += 1;',a)+len('            previous += 1;');frozen=s[a:b]
t=(E/'NHD_distinct.rs.txt').read_text();a=t.index(' if accounts[previous].key() == accounts[index].key() {');b=t.index(' previous += 1;',a)+len(' previous += 1;');native=t[a:b]
project=native.replace('return (Err(ProgramError::InvalidArgument),previous);','return Err(ProgramError::InvalidArgument);')
normalize=lambda x:re.sub(r'\s+','',x)
assert normalize(project)==normalize(frozen)
x=dict(status='PASS_SOURCE_ITERATION_PROJECTION_ONLY',frozen_revision=F,source_path=P,source_sha256=hashlib.sha256(s.encode()).hexdigest(),frozen_iteration_sha256=hashlib.sha256(frozen.encode()).hexdigest(),native_reference_sha256=hashlib.sha256(t.encode()).hexdigest(),projection='Expose the native return as (Result, previous); remove only the retained-previous observation when comparing to the exact frozen inner iteration.',same_comparison_and_increment=True,induction='NGL_DistinctInduction.source',step_association='NHD_DistinctAssociation.associate',bound='previous < index < N <= 7; NHD_DistinctAssociation.increment',native='NHD_K037',inverted='NHD_K038',limitations=['Not a kernel theorem from Rust source','Pointer/array-carrier and pure-key-equality interpretation remain named P6/native associations','Mandatory ruling (t) calibration gate is unfulfilled; no function or row admitted'])
if '--write' in sys.argv:(E/'NHD_SOURCE_ASSOCIATION.json').write_text(json.dumps(x,indent=1)+'\n')
else:assert json.loads((E/'NHD_SOURCE_ASSOCIATION.json').read_text())==x
print(json.dumps(dict(status='PASS',scope='iteration projection only')))
