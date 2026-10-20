from pathlib import Path
import re,hashlib,json
p=Path(__file__).resolve().parent
b=p/'extraction-provenance/chunked-v5'
raw=b/'raw-Funs.lean';types=b/'raw-Types.lean'
h=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
assert h(raw)=='39201df525352aaa34f82d86bce8c09b07d5617a3d89f619d1af9e2f784833c0'
assert h(types)=='cbce0f7d0fee71de2dc0d37a75e7754fa9b7af2bc912fab22f16c471921aafaf'
clean=lambda s:re.sub(r'^set_option (?:maxHeartbeats|maxRecDepth).*\n','',s,flags=re.M)
s=clean(raw.read_text())
# The selected owner inserts exactly one blank framing line before namespace end.
s=s.replace('\nend AspisR1Stage2AdoptedResume\n','\n\nend AspisR1Stage2AdoptedResume\n')
assert s==(p/'sources/QueryValidatorGeneratedPrefix.lean').read_text()
def err(s):
 a=s.index('@[discriminant isize]');z=s.index('| Allocation : verifier.Error',a)+len('| Allocation : verifier.Error');return s[a:z]
assert err(types.read_text())==err((p/'sources/ResumeTypes.lean').read_text())
print('exact generated validator body, resource-option removal, one blank framing line and coherent Error declaration: PASS')
print('Original eager-candidate source/effect equivalence and full resume remain OPEN.')
