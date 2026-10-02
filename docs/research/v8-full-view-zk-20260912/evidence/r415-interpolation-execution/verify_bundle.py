from pathlib import Path
import hashlib, json, re
root=Path(__file__).resolve().parent

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def compact(s): return re.sub(r'\s+', '', s)

def raw_metrics(path):
    s=path.read_text()
    wall=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (\S+)',s)
    rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',s)
    swaps=re.search(r'Swaps: (\d+)',s)
    status=re.search(r'Exit status: (\d+)',s)
    assert all((wall,rss,swaps,status)), f'missing GNU time field in {path}'
    return {'wall_time':wall.group(1),'peak_rss_kib':int(rss.group(1)),'swaps':int(swaps.group(1)),'exit_status':int(status.group(1)),'text':s}

def axiom_reports(log_text):
    return [(name, body) for name,body in re.findall(r"^'([^'\n]+)' depends on axioms: \[([\s\S]*?)\]",log_text,re.M)]

manifest=json.loads((root/'manifest.json').read_text())
for row in manifest['files']:
    p=root/row['path']
    assert p.is_file(), f'missing {row["path"]}'
    assert p.stat().st_size==row['bytes'], f'size mismatch {row["path"]}'
    assert sha(p)==row['sha256'], f'hash mismatch {row["path"]}'
for line in (root/'SHA256SUMS').read_text().splitlines():
    expected,rel=line.split('  ',1)
    assert sha(root/rel)==expected, f'SHA256SUMS mismatch {rel}'

# Exact source and module-path binding to the successful focused inputs.
formal=json.loads((root/'formal.json').read_text())
promoted=root.parent.parent/'lean/AspisV8R19/R415InterpolationExecution.lean'
assert formal['promoted_source_path']=='../../lean/AspisV8R19/R415InterpolationExecution.lean'
assert (root/formal['promoted_source_path']).resolve()==promoted.resolve()
green_source=root/'r415-focused-runs/aspis-focus-1790964117171664000.source.lean'
assert sha(promoted)==formal['source_sha256']==sha(green_source)
assert (root.parent.parent/'lean/AspisV8R19/R415InterpolationExecution.lean').read_bytes()==green_source.read_bytes()
compile_root=root/'generated-module-compiles'
for name in ('Types.lean','Funs.lean'):
    generated=(compile_root/'history'/f'{name}.generated.original').read_bytes()
    adapted=(compile_root/'AspisR403InterpolateThreeLimb'/name).read_bytes()
    extra=(b'import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\nimport Aeneas.Data.Discriminant\n' if name=='Types.lean' else b'import Aeneas.Std\nimport Aeneas.Tactic.RustAttributes\n')
    assert adapted==generated.replace(b'import Aeneas\n',extra,1), f'unapproved source delta {name}'
    promoted_module=root.parent.parent/'lean/AspisR403InterpolateThreeLimb'/name
    assert promoted_module.read_bytes()==adapted, f'promoted module mismatch {name}'

# Verify every generated-module compilation attempt against its raw log, receipt and exact target input.
compile_specs={
 '1790963474979796000':('AspisR403InterpolateThreeLimb/Types.lean',1,'history/Types.lean.adapted-first-attempt'),
 '1790963640381014000':('AspisR403InterpolateThreeLimb/Types.lean',0,'AspisR403InterpolateThreeLimb/Types.lean'),
 '1790963653444949000':('AspisR403InterpolateThreeLimb/Funs.lean',0,'AspisR403InterpolateThreeLimb/Funs.lean'),
}
for aid,(target,status,src_rel) in compile_specs.items():
    rec=json.loads((compile_root/'.r21-scratch'/f'aspis-focus-{aid}.receipt.json').read_text())
    log=raw_metrics(compile_root/'.r21-scratch'/f'aspis-focus-{aid}.log')
    snap=compile_root/'.r21-scratch'/f'aspis-focus-{aid}.source.lean'
    target_bytes=(compile_root/src_rel).read_bytes()
    assert rec['target']==target and rec['exit_status']==status
    assert rec['source_sha256']==sha(snap)==sha(compile_root/src_rel)
    assert log['exit_status']==status==rec['exit_status']
    assert log['wall_time']==rec['wall_time'] and log['peak_rss_kib']==rec['peak_rss_kib'] and log['swaps']==rec['swaps']
    assert target_bytes==snap.read_bytes()
    assert rec['resources']=={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128,'lean_flags':'-j1 -M4500'}
    assert not rec['complete_print_axioms'], 'generated source has no theorem axioms output'
assert 'Unknown attribute `[discriminant]`' in (compile_root/'.r21-scratch/aspis-focus-1790963474979796000.log').read_text()

# Verify both proof attempts' exact raw metrics and every reported axiom name/list.
proof_specs={'1790964080974562000':1,'1790964117171664000':0}
allowed={'propext','Classical.choice','Quot.sound'}
expected_names=[
 'AspisR403InterpolateThreeLimb.aspis_statement.state_only_poseidon.interpolate_three_constant_limb',
 'AspisV8R19.R415InterpolationExecution.reducer_eq_frozen',
 'AspisV8R19.R415InterpolationExecution.from_encode',
 'AspisV8R19.R415InterpolationExecution.accumulator_bound',
 'AspisV8R19.R415InterpolationExecution.interpolation_raw',
 'AspisV8R19.R415InterpolationExecution.interpolation_exact',
]
for aid,status in proof_specs.items():
    rec=json.loads((root/'r415-focused-runs'/f'aspis-focus-{aid}.receipt.json').read_text())
    log=raw_metrics(root/'r415-focused-runs'/f'aspis-focus-{aid}.log')
    snap=root/'r415-focused-runs'/f'aspis-focus-{aid}.source.lean'
    assert rec['source_revision']=='c145fb14be60e3b2553713927228ac62876dbab2'
    assert rec['target']=='AspisV8R19/R415InterpolationExecution.lean'
    assert rec['exit_status']==status and log['exit_status']==status
    assert rec['source_sha256']==sha(snap)
    assert log['wall_time']==rec['wall_time'] and log['peak_rss_kib']==rec['peak_rss_kib'] and log['swaps']==rec['swaps']
    reports=axiom_reports(log['text'])
    assert [name for name,_ in reports]==expected_names
    assert len(rec['complete_print_axioms'])==len(reports)==6
    for (name,body),receipt_line in zip(reports,rec['complete_print_axioms']):
        assert compact(f"'{name}' depends on axioms: [{body}]")==compact(receipt_line), f'axiom report mismatch: {name}'
        found=set(re.findall(r'[A-Za-z][A-Za-z0-9_.]*',body))
        permitted=allowed if status==0 else allowed|{'sorryAx'}
        assert found<=permitted, f'unexpected axiom tokens {found-permitted}'
    if status==0:
        assert rec['source_sha256']==formal['source_sha256']
    else:
        assert 'sorryAx' in reports[-1][1]

llbc=root/'r403-extraction/R403InterpolateThreeConstantLimb.llbc'
assert sha(llbc)=='6bfbbddbcef03a061ab564b40ccea4f7408d28a6a01010ca16229d349c428efa'
post=json.loads((root/'postrun-identity-audit.json').read_text())
postlog=(root/'postrun-identity-audit.log').read_text()
for node in post['artifacts'].values():
    assert node['source_sha256'] in postlog and node['olean_sha256'] in postlog
    assert (post['lean_source_root']+'/'+node['source_path']) in postlog
    assert (post['cache_root']+'/'+node['olean_path']) in postlog
for token in [post['AeneasStd']['CoreConvertNum_source_sha256'],post['AeneasStd']['CoreConvertNum_olean_sha256'],post['AeneasStd']['Discriminant_source_sha256'],post['AeneasStd']['Discriminant_olean_sha256']]:
    assert token in postlog
assert post['artifacts']['R164ProductExecution']['source_sha256']==sha(root/'dependencies/AspisV8R19/R164ProductExecution.lean')
assert json.loads((root/'r415-focused-runs/aspis-focus-1790964117171664000.receipt.json').read_text())['direct_local_import_sha256']['AspisV8R19.R164ProductExecution']==post['artifacts']['R164ProductExecution']['source_sha256']
assert post['artifacts']['R415InterpolationExecution']['source_sha256']==sha(promoted)
assert post['artifacts']['R403Types']['source_sha256']==sha(root.parent.parent/'lean/AspisR403InterpolateThreeLimb/Types.lean')
assert post['artifacts']['R403Funs']['source_sha256']==sha(root.parent.parent/'lean/AspisR403InterpolateThreeLimb/Funs.lean')
green=json.loads((root/'r415-focused-runs/aspis-focus-1790964117171664000.receipt.json').read_text())
assert formal['target']==green['target'] and formal['source_revision']==green['source_revision']
assert formal['exit_status']==green['exit_status'] and formal['wall_time']==green['wall_time']
assert formal['peak_rss_kib']==green['peak_rss_kib'] and formal['swap_count']==green['swaps']
assert formal['resources']==green['resources']
assert formal['theorems_and_complete_axioms']==[{'name':name,'axioms':[a.strip() for a in body.replace('\n',' ').split(',')]} for name,body in axiom_reports((root/'r415-focused-runs/aspis-focus-1790964117171664000.log').read_text())]
assert sha(root/'frozen-r117-source/crates/aspis-core/src/field.rs')=='639b6425fe672e0fa6019b99b702d1f08f56cd75c4d9ad6defef854b7640f499'
assert sha(root/'frozen-r117-source/crates/aspis-statement/src/state_only_poseidon.rs')=='4467d15c9d473cbd42caf33f21aa0192bed007b58ccaa4a61cb5691532cab7fe'
print(f'PASS files={len(manifest["files"])} proof_attempts={len(proof_specs)} generated_compile_attempts={len(compile_specs)} green_axiom_reports=6 source_snapshots=all exact postrun_cache_identity=yes')
