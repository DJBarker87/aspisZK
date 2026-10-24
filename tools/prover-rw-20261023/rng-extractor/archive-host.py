"""Read-only collection after build-budget exhaustion; no validation launch."""
from pathlib import Path
import difflib,hashlib,json,subprocess
D=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/rng-extractor')
T=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full')
provenance=json.loads((D/'base-provenance.json').read_text())
build3=json.loads((D/'prover-rw-rng-extractor-build-003/receipt.json').read_text())
build4=json.loads((D/'prover-rw-rng-extractor-build-004/receipt.json').read_text())
pin=lambda p:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
patches={3:[],4:[]}
snapshots={3:{},4:{}}
for rel,expected in provenance['source_manifest'].items():
    if 'sha256' not in expected:continue
    orig=T/rel
    assert pin(orig)==expected, ('Base moved after pin',rel)
    p=D/'base'/rel
    text=p.read_text() if p.suffix in ['.ml','.mli'] else None
    for attempt in [3,4]:
        data=p.read_bytes()
        if attempt==3 and rel=='src/llbc/TypesAnalysis.ml':
            s=data.decode()
            a=s.index('    let retained_refined_record =')
            b=s.index('\n  in\n  let has_regions',a)
            data=(s[:a]+'    !Config.use_tuple_structs && (not is_rec) && type_decl_is_tuple_struct def'+s[b:]).encode()
        sha=hashlib.sha256(data).hexdigest()
        receipt=build3 if attempt==3 else build4
        assert receipt['candidate_source_sha256'][rel]==sha,(attempt,rel)
        snapshots[attempt][rel]=dict(sha256=sha,bytes=len(data))
        if sha!=expected['sha256']:
            patches[attempt].extend(difflib.unified_diff(orig.read_text().splitlines(True),data.decode().splitlines(True),fromfile='a/'+rel,tofile='b/'+rel))
for attempt,lines in patches.items():
    (D/f'candidate-{attempt:03d}.patch').write_text(''.join(lines))
    (D/f'candidate-{attempt:03d}-source-manifest.json').write_text(json.dumps(snapshots[attempt],indent=2)+'\n')
binary=D/'base/src/_build/default/main.exe'
assert pin(binary)['sha256']=='09af4fe5a40f2340b3b326e01b15b23d8e8a0a39e3ae25938f9033dd56d5fdc5'
out=dict(binary=pin(binary),binary_source='candidate-003.patch; build003 succeeded; build004 failed before replacing binary',
    binary_version=subprocess.check_output([str(binary),'-version'],text=True).strip(),
    source4='candidate-004.patch; record-preservation change is unbuilt, failed opaque disambiguator match',
    reproducibility='Pinned base + complete accepted extensions + exact candidate patch + pinned compiler dependency image and opam package inventory. Fresh isolated build succeeded for candidate003. No independent deterministic rebuild or historical byte-reproducibility claim.',
    no_more_builds='4/4 ceiling exhausted: stop for lead review. No source repair or build005 launched.',
    print_axioms='N/A: no Lean invocation or new checked theorem')
(D/'candidate-pins.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
