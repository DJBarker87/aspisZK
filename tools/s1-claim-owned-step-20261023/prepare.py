#!/usr/bin/env python3
"""Native complete-carrier original/owned one-step coupling."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1])
subprocess.run(['python3',str(R/'tools/s1-claim-replay-20261023/prepare.py'),str(O)],check=True)
source=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/s1-claim-uf/inputs/s1-claim-owned-nested-v7/input/lib.rs'
s=source.read_text();a=s.index('fn owned_scalar(');b=s.index('fn prepared_claim<',a);fragment=s[a:b]
step='''
fn owned_step<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:[u8;928],g:[E;29],point:usize,l:usize,dot:crate::fast_pairing::EbyKDot)->(Result<(),Error>,crate::fast_pairing::EbyKDot) {
 let scalar=owned_scalar(*sem.claims,sem.extra,sem.before_z1,y1,point,l);
 let (r,dot)=owned_push(dot,g,l,scalar);
 (r.map_err(|_|Error::Parse),dot)
}
'''
p=O/'src/lib.rs';p.write_text(p.read_text()+fragment+step)
(O/'src/proofs.rs').write_bytes((Path(__file__).parent/'proofs.rs').read_bytes())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(O/'owned-step-binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',
    owned_source_sha256=sha(source),owned_fragment=fragment,owned_step=step,
    source_sha256=sha(O/'src/lib.rs'),proof_sha256=sha(O/'src/proofs.rs'),
    qualification='Arbitrary complete native Dot state, full actual Verified carrier, all six points/all29 columns, arbitrary common push error/poststate and field-frame output. No simplified semantic carrier. Actual leaf contracts, loop/caller source transport and release pins remain explicit.'),indent=2)+'\n')
if '--frozen-statement' in sys.argv[2:]:
    rev='25866ec331cc7ce27dd9956609c11d32fa8fa58a'
    prefix='crates/aspis-statement/'
    get=lambda p:subprocess.check_output(['git','-C',str(R),'show',rev+':'+p])
    dest=O/'frozen-source/crates/aspis-statement';dest.mkdir(parents=True)
    files=subprocess.check_output(['git','-C',str(R),'ls-tree','-r','--name-only',rev,prefix],text=True).splitlines()
    pins={}
    for name in files:
        if not name.endswith('.rs'):continue
        p=dest/Path(name).relative_to(prefix);p.parent.mkdir(parents=True,exist_ok=True)
        p.write_bytes(get(name));pins[str(p.relative_to(dest))]=sha(p)
    base='/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src/'
    manifest=get(prefix+'Cargo.toml').decode().replace('edition.workspace = true','edition = "2021"').replace('license.workspace = true','license = "MIT OR Apache-2.0"').replace('version.workspace = true','version = "0.1.0-s1-freeze"')
    manifest=manifest.replace('aspis-core.workspace = true','aspis-core = { path = "'+base+'crates/aspis-core" }').replace('sha2.workspace = true','sha2 = "0.10.8"')
    from posixpath import normpath
    manifest=re.sub(r'path = "(\.\./[^"]+)"',lambda m:'path = "'+normpath(base+prefix+m[1])+'"',manifest)
    (dest/'Cargo.toml').write_text(manifest)
    p=O/'frozen-probe/Cargo.toml';text=p.read_text();old=base+'crates/aspis-statement'
    assert text.count(old)==1
    p.write_text(text.replace(old,'../frozen-source/crates/aspis-statement'))
    # Keep this dependency outside the proof workspace, as in the original
    # external cached dependency. Otherwise Cargo resolves its unrelated dev
    # tests, including a yanked spin dependency, for this --lib-only check.
    root_manifest=O/'Cargo.toml'
    root_manifest.write_text(root_manifest.read_text().replace('[workspace]\n','[workspace]\nexclude=["frozen-source/crates/aspis-statement"]\n'))
    external={}
    source_root=O/'frozen-source'
    queue=list(dest.rglob('*.rs'))
    # Preserve repository-relative Rust include/path imports transitively.
    seen=set()
    while queue:
        current=queue.pop()
        if current in seen:continue
        seen.add(current)
        text=current.read_text()
        refs=re.findall(r'include!\(\s*"([^"]+\.rs)"',text)+re.findall(r'#\[path\s*=\s*"([^"]+\.rs)"\]',text)
        for ref in refs:
            relative=normpath(str(current.relative_to(source_root).parent)+'/'+ref)
            assert not relative.startswith('../'),relative
            p=source_root/relative
            if not p.exists():
                p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(get(relative))
                external[relative]=sha(p)
            queue.append(p)
    (O/'frozen-statement-binding.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',revision=rev,source_files=pins,external_source_files=external,manifest_sha256=sha(dest/'Cargo.toml'),qualification='Exact adopted statement Rust sources; manifest workspace metadata and local dependency paths only are materialized. A proof-only prerelease package version avoids collision with the inactive optional host-prover dependency on the cached statement crate. Replaces the known six-file drift in the cached dependency.'),indent=2)+'\n')
