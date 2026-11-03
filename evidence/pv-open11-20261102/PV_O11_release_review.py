"""Check adopted source identities; never promotes identity to a release proof."""
from pathlib import Path
import subprocess,json,hashlib
D=Path(__file__).parent;S=D/'inputs/release';S.mkdir(exist_ok=True)
rev='45336b1249'
pins={}
def get(path):
    b=subprocess.check_output(['git','show',rev+':'+path]);p=S/Path(path).name
    assert not p.exists() or p.read_bytes()==b
    p.write_bytes(b)
    pins[path]=dict(revision=rev,blob=subprocess.check_output(['git','rev-parse',rev+':'+path],text=True).strip(),sha256=hashlib.sha256(b).hexdigest(),snapshot=str(p.relative_to(D)))
    return json.loads(b) if path.endswith('.json') else b.decode()
old=get('evidence/pv-mf-20261029/REPORT.md')
review=get('evidence/pv-mfe-20261029/STALE-REVIEW-4.md')
adopted=get('evidence/pv-c474b-20261029/final-audit.json')
expected=get('evidence/pv-c474b-20261029/expected-sources.json')
correction=get('evidence/pv-c474b-20261029/audit-manifest-correction.json')
audit_builder=get('tools/pv-c474b-20261029/harness-build.py')
assert len(expected)==1284
assert adopted['client']['sha256']=='da36d6aa36f8566ffa2ce7276546941c745bcd6325613c5a98c5517328b7def0'
assert '76 A, 657 B, 31 C' in review and '31 records remain C' in review
assert 'V346 remains P / OPEN' in old
proc=subprocess.Popen(['git','cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE)
results=[]
for path,want in expected.items():
    proc.stdin.write((rev+':'+path+'\n').encode());proc.stdin.flush()
    header=proc.stdout.readline().decode().strip();parts=header.split()
    if parts[-1]=='missing':
        results.append(dict(path=path,expected=want,missing=True,equal=False));continue
    blob,kind,size=parts;assert kind=='blob';data=proc.stdout.read(int(size));assert proc.stdout.read(1)==b'\n'
    actual=hashlib.sha256(data).hexdigest()
    results.append(dict(path=path,blob=blob,sha256=actual,expected=want,equal=actual==want))
proc.stdin.close();assert proc.wait()==0
different=[x for x in results if not x['equal']]
assert len(different)==15 and all(x.get('missing') for x in different)
assert all(x['path'].startswith(('tools/r1-cost-probe-base/','tools/pv-c474-validation/')) for x in different)
assert all(x['equal'] for x in results if x['path'].startswith(('crates/','programs/','tools/r1-cost-probe/')))
assert correction['production_source_changed'] is False and "V=R/'tools/pv-c474-validation'" in audit_builder
rows={
 'V346':dict(rank=18,status='OPEN',exact_premise='Produce a current proved=shipped manifest joining the adopted da36d6aa client, exact toolchain/profile/resolved features, three retained ELFs, protocol/wire parameters, every actually reached native source/extraction/reference binding and decoder, endpoint declarations and all accepted proof/effect/trace certificates. Retain the 31 unresolved provenance/audit-consumer cases, K-3 suspensions, V370, E1/E2 and current source/cohort qualifications. Finish one coherent dependency replay plus NEP importAll/private HARD-ERROR audit at the same adopted release. Equality of 1284 listed source inputs is identity evidence only: it neither certifies complete reachability nor installs missing native links, and the old fa888460 manifest/replay or successful cached imports do not transfer by name.'),
 'V340':dict(rank=19,status='OPEN',exact_premise='Bind final candidate/research adoption to the SAME current event-retaining deployed headline, adopted da36d6aa artifact and effective features/profile, actual proof-account caller/upload route and all release conditions. D502 timing/recipe decisions and D537 bundle adoption settle those historical decisions only; current user-client adoption, E1/E2, coherent theorem/native-instance/source/artifact association and full L1/L2/L3 joint observation remain. The old empty shipped-source diff supports only its pinned evidence reuse. Do not merge/rebase another line or declare the research target adopted from source equality; preserve the endpoint, simulator, observer, bound and capped three-field T.')}
out=dict(classification='source identity and retained release-statement inspection only; no full manifest replay or native binding',
 revision=rev,pins=pins,source_identity=results,source_count=len(results),equal_count=len(results)-len(different),different=different,
 missing_classification='15 listed baseline/comparison or audit-harness paths absent from this git tree; no changed present source or production mismatch established. The audit builder reconstructs validation Cargo.toml; no missing input is silently substituted or claimed reproduced.',
 rows=rows,attempts={r:dict(inspections=1,lean=0,native=0) for r in rows},
 restored=0,premises_removed=0,premises_added=0,premises_weakened=0,next_rank=20,next_row='V347')
(D/'PV_O11_release-review.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(ok=True,source_count=len(results),equal_count=len(results)-len(different),different_paths=[r['path'] for r in different],restored=0)))
