"""Explicit staging/import-only continuation; run locally, never compiles Lean."""
import json,hashlib,subprocess,re
from pathlib import Path
D=Path(__file__).resolve().parent; R=Path.cwd(); base='docs/research/100bit-spend-path-20261013/'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
extras={}
for owner,folder in {
'AspisR1RowShape':'evidence/lean-record-source-20261015/row-and-parser-e',
'AspisR1RecordParser':'evidence/lean-record-source-20261015/header-parser-f',
'AspisR1WithdrawalValidation':'evidence/withdrawal-validation-source-431-20261015/extraction/attempt-c-fixed-digest/generated',
'AspisR1PublicSerializer':'evidence/lean-public-serializer-source-20261015',
}.items():
 for part in ['Types','Funs']:extras[owner+'.'+part]=base+folder+'/'+owner+'/'+part+'.lean'
for n in ['R22FastPairingPrimitiveBounds','R22CanonicalQM31','R22CanonicalCM31','R22CurrentReducerMul','R22CanonicalM31AddSub','CheckedWrappingScalarAgreement']:
 extras[n]=base+'lean-candidates/r22-current-field-wrapping-20261019/'+n+'.lean'
# Recover original retained inputs, never synthesize a theorem.
remote={
 'RRBoundedSliceScannerV5':'/tmp/rrfinal-native-sources-20261019/concrete-closure/RRBoundedSliceScannerV5.lean',
 'CompPolyModularRemainderDegree':'/home/dombarker/project-offloads/root-extractor-gcd-normalization-v4-20261019/provenance/CompPolyModularRemainderDegree.lean'}
(D/'retained-inputs').mkdir(exist_ok=True)
for n,p in remote.items():
 dst=D/'retained-inputs'/(n+'.lean')
 subprocess.run(['scp','dombarker@100.108.41.90:'+p,str(dst)],check=True)
 extras[n]=str(dst.relative_to(R))
# Only import header changes. Body is identical, checked below.
p=R/base/'lean/LiteralTranscript.lean';old=p.read_text()
if 'import R1UnifiedSampler\n' not in old:p.write_text(old.replace('import R1SelectedTranscriptParams\n','import R1SelectedTranscriptParams\nimport R1UnifiedSampler\n'))
assert '\n'.join(l for l in p.read_text().splitlines() if not l.startswith('import '))=='\n'.join(l for l in old.splitlines() if not l.startswith('import '))
# Extend existing manifest resolver with explicit evidence owners; library is the retained external package.
p=D/'manifest.py';s=p.read_text()
marker='# Continuation explicit evidence source owners\n'
if marker in s:s=s[:s.index(marker)] # script updates below use separate resolver, original preserved
s=s.replace("'Aeneas', 'AeneasMeta')","'Aeneas', 'AeneasMeta', 'CompPoly')")
needle='def imports_of(path):'
inject='''# Explicit source ownership authorized for the continuation; generated files unchanged.\nfor n, rel in json.load(open(os.path.join(a.repo, "'''+str((D/'continuation-owners.json').relative_to(R))+'''"))).items():\n    index[n] = [('spend', 'explicit-evidence', rel, sha(os.path.join(a.repo, rel)))]\n'''
s=s.replace(needle,inject+needle)
(D/'manifest-continuation.py').write_text(s)
(D/'continuation-owners.json').write_text(json.dumps(extras,indent=2)+'\n')
oldman=json.loads((D/'manifest-S.json').read_text())
if not (D/'manifest-phase1.json').exists():(D/'manifest-phase1.json').write_text(json.dumps(oldman,indent=1)+'\n')
roots=','.join(oldman['roots'])
cmd=['python3',str(D/'manifest-continuation.py'),'--repo','.', '--roots',roots,'--require-complete','--out',str(D/'manifest-S.json')]
r=subprocess.run(cmd,capture_output=True,text=True)
(D/'continuation-preflight.json').write_text(json.dumps({'command':cmd,'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr},indent=2)+'\n')
print(r.stdout,r.stderr)
(D/'retained-input-provenance.json').write_text(json.dumps({n:{'host_source':p,'sha256':sha(D/'retained-inputs'/(n+'.lean'))} for n,p in remote.items()},indent=2)+'\n')
