from pathlib import Path
import re,json,hashlib,subprocess
r=Path(__file__).resolve().parent
repo=r
while not (repo/'.git').exists():repo=repo.parent
frozen='c8ea8dd49c81ab970b9dbee8d8b47718f9beb005'
h=lambda b:hashlib.sha256(b).hexdigest()
b=r/'worker-archives/push-control';pins=json.loads((b/'rust-input/source-pins.json').read_text())
for name,pin in pins['source_files'].items():assert h(subprocess.check_output(['git','show',frozen+':'+name],cwd=repo))==pin
for name,pin in pins['kit_files'].items():assert h((b/'rust-input'/name).read_bytes())==pin
original=subprocess.check_output(['git','show',frozen+':crates/aspis-r1-cost-probe/src/fast_pairing.rs'],cwd=repo).decode()
fragment=original[original.index('mod canonical {'):original.index('/// Candidate exact accumulator for sums of `WideExact * WideExact`.')].replace('aspis_core::field','crate::field')
assert fragment in (b/'rust-input/lib.rs').read_text()
raw=(b/'generated/Funs.lean').read_text();ad=(r/'sources/AspisR1EbyKPushWideToQ.lean').read_text()
def body(s,start,end):
 s=s[s.index(start):];s=s[:s.index(end)];return s.split(':= do',1)[1].strip()
def norm(s):return ' '.join(re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*|[0-9]+#[A-Za-z0-9_]+|[0-9]+|[^\s]",s))
a=body(raw,'def field.wide_exact.WideExact.to_limbs','/--')
bb=body(ad,'def toLimbs','def fromWide');assert norm(a)==norm(bb)
a=body(raw,'def fast_pairing.canonical.Q.from_wide','/--').replace('field.wide_exact.WideExact.to_limbs','toLimbs')
bb=body(ad,'def fromWide','def qFromCoords');assert norm(a)==norm(bb)
for name in ['Types','Funs']:
 b=r/'worker-archives/constructor/lean';raw1=(b/'raw-generated'/(name+'.lean')).read_text()
 clean=re.sub(r'^set_option (?:maxHeartbeats|maxRecDepth) .*\n','',raw1,flags=re.M)
 assert clean==(r/'sources/AspisR1Stage2Accumulate'/(name+'.lean')).read_text()
raw1=(r/'worker-archives/push-control/generated/Types.lean').read_text()
clean=re.sub(r'^set_option (?:maxHeartbeats|maxRecDepth) .*\n','',raw1,flags=re.M)
assert clean==(r/'sources/EbyKPushExplicitTypesV1.lean').read_text()
print('Frozen source pins, complete copied conversion bodies and resource-line-only generated adapters: PASS')
