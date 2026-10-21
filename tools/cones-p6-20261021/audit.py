#!/usr/bin/env python3
"""Audit focused composition evidence, without replaying inherited jobs."""
import hashlib,json,re,subprocess
from pathlib import Path
R=Path(__file__).resolve().parents[2]
B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/multiproof-cone-20261021'
BASE='4ca5d2e35'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def rust_body(path,signature):
    s=(R/path).read_text(); start=s.index(signature); begin=s.index('{',start)
    depth=1; end=begin+1
    while depth:
        depth+=(s[end]=='{')-(s[end]=='}');end+=1
    body=s[start:end]
    return dict(path=path,signature=signature,start_line=s.count('\n',0,start)+1,
                end_line=s.count('\n',0,end)+1,body_sha256=hashlib.sha256(body.encode()).hexdigest())
rows=[]
for path,sig,cone,disposition in [
 ('crates/aspis-r1-cost-probe/src/verifier.rs','fn for_range(', 'S7','Gather/lookup/opaque-inv/source adoption open; reciprocal Vec port proved'),
 ('crates/aspis-r1-cost-probe/src/candidate.rs','fn query_values(', 'S7','S4 four_dots, physical opening/fold/guard and carrier adoption open'),
 ('crates/aspis-r1-cost-probe/src/verifier.rs','fn accumulate_batched_with_node(', 'S7','Complete carrier-port iteration proved; original source/observer lowering open'),
 ('crates/aspis-r1-cost-probe/src/verifier.rs','fn circle_fold_with_inverses(', 'S7','Field algebra retained; emitted raw backend-to-field source join open'),
 ('crates/aspis-r1-cost-probe/src/verifier.rs','fn line_fold_with_inverses(', 'S7','Field algebra retained; emitted raw backend-to-field source join open'),
 ('crates/aspis-r1-cost-probe/src/verifier.rs','fn value(&self,index:', 'S8','Whole owned value and mutable finish certificates retained'),
 ('crates/aspis-r1-cost-probe/src/verifier.rs','fn finish(&self,weights:', 'S8','Returned-state finish-port stage equality proved'),
 ('crates/aspis-r1-cost-probe/src/compact.rs','pub fn check_values(', 'S8','Whole strict-scan reference certificate retained'),
 ('crates/aspis-r1-cost-probe/src/verifier.rs','fn finish_query_dot(', 'S8','Actual EbyKDot new/push/finish and decoded-value/raw/count semantics open (S5 dependency)'),
 ('crates/aspis-r1-cost-probe/src/verifier.rs','pub fn finish_relation(', 'S8','S3/S5/S9 pairing/round gates and final dot source composition open'),
 ('crates/aspis-r1-cost-probe/src/verifier.rs','pub fn checkpoint<', 'checkpoint','Nested K writer certified; remaining E/body/C5 blocks and reached Prepared/accumulator canonicality open'),
 ('crates/aspis-r1-cost-probe/src/verifier.rs','pub fn resume<', 'checkpoint','Bounded decoder/section/authentication gates retained; complete source reader/allocation/interleaving/C5 adoption open'),
]:
    rows.append(dict(cone=cone,disposition=disposition,**rust_body(path,sig)))
translation=B/'evidence/s7-kani-20261021/extraction/generated/translation.json'
t=json.loads(translation.read_text())
opaque=[x['lean_name'] for x in t['functions'] if x.get('is_opaque')]
# This is a concrete extraction boundary, not a claim that all independent
# replacement ports are absent or that opaque declarations are inconsistent.
missing_external=[str(p.relative_to(R)) for p in [translation.parent/'S7OwnedP6/TypesExternal.lean',
    translation.parent/'S7OwnedP6/FunsExternal.lean'] if not p.exists()]
manifest=json.loads((E/'cones-p6-manifest.json').read_text())
accepted=[]
expected=['S7P6AccumulatorIterations','S8P6ReturnedFinish','CheckpointP6EncodeK','CheckpointP6KBytes','ConesP6FocusedFreeze']
for name in expected:
    candidates=[x for x in manifest['attempts'] if x['module']==name and x['final_current']]
    assert len(candidates)==1,(name,'missing unique current success')
    a=candidates[0];source=B/'lean'/f'{name}.lean'
    assert a['exit']==0 and a['swaps']==0 and a['source_sha256']==sha(source)
    snapshot=E/f"{name}-{a['attempt']}"/'source.lean.txt'
    assert source.read_bytes()==snapshot.read_bytes()
    assert a['axioms'] and not a['errors']
    for line in a['axioms']:
        if 'depends on axioms:' in line:
            names=set(re.search(r'\[([^]]*)\]',line)[1].replace(' ','').split(','))
            assert names<=set(['propext','Classical.choice','Quot.sound']),(name,line)
    text=source.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|maxHeartbeats|maxRecDepth)\b',text)
    for imported in a['direct_imports']:
        assert sha(Path(imported['path']))==imported['sha256']
    for dep in a['owned_transitive_dependencies']:
        assert sha(R/dep['source'])==dep['source_sha256']
        assert sha(Path(dep['object']))==dep['object_sha256']
    accepted.append({k:a[k] for k in ['module','attempt','exit','source_revision','source_sha256',
        'deps_fingerprint','wall_seconds','peak_rss_bytes','swaps','axioms']})
changes=subprocess.check_output(['git','diff','--name-only',BASE],cwd=R,text=True).splitlines()
for name in changes:
    assert (name.startswith('tools/cones-p6-20261021/') or
        name.startswith(str(E.relative_to(R))+'/') or
        name==str((B/'design/CONE-AUDIT-20261021.md').relative_to(R)) or
        name in [str((B/'lean'/f'{m}.lean').relative_to(R)) for m in expected]), name
shipped=subprocess.check_output(['git','diff',BASE,'--','crates','programs'],cwd=R,text=True)
assert not shipped
report=dict(schema='cones-p6-focused-composition-audit-v1',base=BASE,
    audited_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
    status='PARTIAL: no whole-source S7/S8/checkpoint certificate or AcceptedRunJoin',
    frozen_elf_gate_triggered=False,source_functions=rows,
    inherited_s7_extraction=dict(path=str(translation.relative_to(R)),sha256=sha(translation),
        opaque_functions=opaque,opaque_count=len(opaque),missing_import_sources=missing_external),
    accepted=accepted,changed_paths=changes,
    failed_attempts=[dict(module=a['module'],attempt=a['attempt'],exit=a['exit'],
        source_sha256=a['source_sha256']) for a in manifest['attempts'] if a['exit']!=0])
(E/'cones-p6-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(status=report['status'],modules=len(accepted),
    theorem_reports=sum(len(a['axioms']) for a in accepted),
    peak_rss_bytes=max(a['peak_rss_bytes'] for a in accepted),swaps=0)))
