#!/usr/bin/env python3
"""Discover frozen Cargo closure from Git; transport, validate, and extract it.
Host operations must run through an admitted capped launcher, never directly.
Only --export reads Git. All other modes consume the committed frozen payload.
"""
from pathlib import Path, PurePosixPath
import argparse, base64, fnmatch, hashlib, json, lzma, os, posixpath, re, subprocess, sys, tomllib
REV = '4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
E = Path(__file__).resolve().parent
FEATURES = 'private-leaf-salts,optimized-terminal,program-build'
TOOLROOT = Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin')
PINS = {'charon':'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8', 'aeneas-b59d5188-extended':'c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'}
ALLOWED_MISSING = {('aspis-r1-cert-build','0.0.0',None), ('aspis-r1-cert-check','0.0.0',None), ('aspis-z4b-probe','0.1.0',None)}
def sha(data): return hashlib.sha256(data).hexdigest()
def write(p, obj):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(obj, indent=2, sort_keys=True)+'\n')
def safe(p):
    assert p and not p.startswith('/') and '..' not in PurePosixPath(p).parts, p
    return p

def dependency_paths(v):
    if not isinstance(v,dict): return
    for table, entries in v.items():
        if table in ('dependencies','dev-dependencies','build-dependencies','replace'):
            for dep in entries.values():
                if isinstance(dep,dict) and isinstance(dep.get('path'),str): yield dep['path']
        elif table == 'patch':
            for registry in entries.values():
                for dep in registry.values():
                    if isinstance(dep,dict) and isinstance(dep.get('path'),str): yield dep['path']
        elif isinstance(entries,dict): yield from dependency_paths(entries)

def export():
    def git(*args): return subprocess.check_output(['git',*args])
    listing = git('ls-tree','-rz',REV).split(b'\0')
    tree = {}
    for row in listing:
        if not row: continue
        meta, path = row.split(b'\t'); mode, kind, oid = meta.decode().split()
        if kind == 'blob': tree[path.decode()] = (mode, oid)
    def blob(p): return git('cat-file','blob',tree[safe(p)][1])
    root = tomllib.loads(blob('Cargo.toml').decode())
    manifests = {p for p in tree if p.endswith('/Cargo.toml')}
    roots = set()
    for pattern in root['workspace']['members']:
        matched = {str(PurePosixPath(p).parent) for p in manifests if fnmatch.fnmatchcase(str(PurePosixPath(p).parent),pattern)}
        assert matched, ('missing workspace member',pattern)
        roots.update(matched)
    members = sorted(roots); queue = list(roots)
    # Include root workspace.dependencies, patch/replace and target-specific tables.
    for rel in dependency_paths(root):
        p = safe(posixpath.normpath(rel))
        if p not in roots: roots.add(p); queue.append(p)
    edges = []
    while queue:
        d = queue.pop(); m = tomllib.loads(blob(d+'/Cargo.toml').decode())
        for rel in dependency_paths(m):
            p = safe(posixpath.normpath(posixpath.join(d,rel)))
            assert p+'/Cargo.toml' in tree, ('missing path manifest',d,rel)
            edges.append([d,p])
            if p not in roots: roots.add(p); queue.append(p)
    selected = {'Cargo.toml','Cargo.lock'}
    selected.update(p for p in tree if any(p.startswith(d+'/') for d in roots))
    # Include literal Rust inputs outside package roots, recursively.
    queue = list(selected)
    while queue:
        p = queue.pop()
        if not p.endswith('.rs'): continue
        text = blob(p).decode()
        for rel in re.findall(r'include(?:_str|_bytes)?!\s*\(\s*"([^"]+)"',text):
            q = safe(posixpath.normpath(posixpath.join(posixpath.dirname(p),rel)))
            assert q in tree, ('missing include',p,q)
            if q not in selected: selected.add(q); queue.append(q)
    data = {}; pins = {}
    # All tracked files in each package are retained, including fixtures and build inputs.
    for p in sorted(selected):
        raw = blob(p); mode, oid = tree[p]
        assert mode in ('100644','100755'), ('unsupported mode',p,mode)
        data[p] = base64.b64encode(raw).decode()
        pins[p] = dict(sha256=sha(raw),bytes=len(raw),git_blob=oid,mode=mode)
    manifest = dict(revision=REV,workspace_members=members,package_roots=sorted(roots),path_edges=sorted(edges),files=pins)
    raw = json.dumps(data,sort_keys=True).encode()
    (E/'NMX_FROZEN_PAYLOAD.json.xz').write_bytes(lzma.compress(raw,preset=6))
    (E/'NMX_FROZEN_PAYLOAD.json.sha256').write_text(sha(raw)+'\n')
    write(E/'NMX_STAGING_MANIFEST.json',manifest)
    print(json.dumps(dict(packages=len(roots),files=len(data),bytes=sum(p['bytes'] for p in pins.values()))))

def stage(workspace):
    manifest = json.loads((E/'NMX_STAGING_MANIFEST.json').read_text())
    assert manifest['revision']==REV
    raw = lzma.decompress((E/'NMX_FROZEN_PAYLOAD.json.xz').read_bytes())
    assert sha(raw)==(E/'NMX_FROZEN_PAYLOAD.json.sha256').read_text().strip()
    payload = json.loads(raw); assert set(payload)==set(manifest['files'])
    workspace.mkdir(parents=True,exist_ok=True)
    for p, info in manifest['files'].items():
        target = workspace/safe(p); data = base64.b64decode(payload[p],validate=True)
        assert sha(data)==info['sha256'] and len(data)==info['bytes']
        # Verify the Git blob ID independently of the SHA256 transport manifest.
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==info['git_blob']
        target.parent.mkdir(parents=True,exist_ok=True)
        if target.exists(): assert target.read_bytes()==data, ('staged drift',p)
        else: target.write_bytes(data); target.chmod(int(info['mode'],8)&0o777)
    # Re-enumerate from staged manifests in --check, independently of exported roots.
    root = tomllib.loads((workspace/'Cargo.toml').read_text())
    roots = set()
    for pattern in root['workspace']['members']:
        matches = {str(p.relative_to(workspace)) for p in workspace.glob(pattern) if (p/'Cargo.toml').is_file()}
        assert matches, ('missing staged member',pattern)
        roots.update(matches)
    assert roots==set(manifest['workspace_members'])
    roots.update(safe(posixpath.normpath(x)) for x in dependency_paths(root))
    queue = list(roots)
    while queue:
        d = queue.pop(); doc = tomllib.loads((workspace/d/'Cargo.toml').read_text())
        for rel in dependency_paths(doc):
            q = safe(posixpath.normpath(posixpath.join(d,rel)))
            assert (workspace/q/'Cargo.toml').is_file(), ('missing staged dependency',d,q)
            if q not in roots: roots.add(q); queue.append(q)
    assert roots==set(manifest['package_roots']), 'staged manifest closure differs'
    return manifest

def validate(workspace, out, cargo, function=None):
    manifest = stage(workspace)
    expected = manifest['files']['Cargo.lock']['sha256']
    package = 'programs/r1-cost-probe' if function in ['entry','process','auth','lane','registry'] else 'crates/aspis-r1-cost-probe'
    features = 'pool-adapter,private-leaf-salts' if function in ['entry','process','auth','lane','registry'] else FEATURES
    cmd = [cargo,'+1.94.1','metadata','--manifest-path',str(workspace/package/'Cargo.toml'),'--locked','--offline','--format-version','1','--features',features]
    r = subprocess.run(cmd,capture_output=True,text=True,env={**os.environ,'CARGO_NET_OFFLINE':'true'})
    (out/'metadata.stderr').write_text(r.stderr); (out/'metadata.stdout').write_text(r.stdout)
    assert sha((workspace/'Cargo.lock').read_bytes())==expected, 'STOP lock drift'
    assert r.returncode==0, r.stderr
    m = json.loads(next(l for l in r.stdout.splitlines() if l.startswith('{')))
    write(out/'metadata.json',m)
    key = lambda p:(p['name'],p['version'],p.get('source'))
    frozen = {key(p):p for p in tomllib.loads((workspace/'Cargo.lock').read_text())['package']}
    actual = {key(p):p for p in m['packages']}; pkgs = {p['id']:p for p in m['packages']}
    nodes = {n['id']:n for n in m['resolve']['nodes']}; errors = []
    for p in m['packages']:
        if key(p) not in frozen: continue
        for dep in nodes[p['id']]['dependencies']:
            q = pkgs[dep]
            labels = [s.split(' ') for s in frozen[key(p)].get('dependencies',[])]
            if not any(v[0]==q['name'] and (len(v)<2 or v[1]==q['version']) and (len(v)<3 or v[2].strip('()')==q.get('source')) for v in labels): errors.append([key(p),key(q)])
    disabled = tomllib.loads((workspace/'crates/aspis-r1-cost-probe/Cargo.toml').read_text())['dependencies']['aspis-z4b-probe']['optional'] is True and not any('r1p-check' in n['features'] for n in nodes.values())
    added = set(actual)-set(frozen); missing = set(frozen)-set(actual)
    ok = not added and not (missing-(ALLOWED_MISSING if disabled else set())) and not errors
    report = dict(command=cmd,graph_matches_frozen=ok,added=sorted(added,key=str),missing=sorted(missing,key=str),edge_errors=errors,lock_before=expected,lock_after=sha((workspace/'Cargo.lock').read_bytes()),features=[dict(name=pkgs[i]['name'],version=pkgs[i]['version'],features=n['features']) for i,n in nodes.items()],validated_files=len(manifest['files']),revision=REV)
    write(out/'NMX_GRAPH_CHECK.json',report)
    assert ok, report
    return manifest

def options(args, workspace, out):
    selection = {'lane': ('crate::r1_pool_adapter::decode_lane_from_pool_release', 'programs/r1-cost-probe', 'pool-adapter,private-leaf-salts', 'aspis_r1_cost_probe_program'), 'registry': ('crate::r1_pool_adapter::owned::authenticate_invariant_release_registry', 'programs/r1-cost-probe', 'pool-adapter,private-leaf-salts', 'aspis_r1_cost_probe_program'), 'auth': ('crate::r1_pool_adapter::owned::authenticate_asq8_accounts', 'programs/r1-cost-probe', 'pool-adapter,private-leaf-salts', 'aspis_r1_cost_probe_program'), 'process': ('crate::r1_pool_adapter::process', 'programs/r1-cost-probe', 'pool-adapter,private-leaf-salts', 'aspis_r1_cost_probe_program'), 'entry': ('crate::process_r1_cost_probe_instruction', 'programs/r1-cost-probe', 'pool-adapter,private-leaf-salts', 'aspis_r1_cost_probe_program'), 'debug': ('crate::verifier::_::fmt', 'crates/aspis-r1-cost-probe', FEATURES, 'aspis_r1_cost_probe'), 'error': ('crate::error', 'programs/r1-cost-probe', 'pool-adapter,private-leaf-salts', 'aspis_r1_cost_probe_program')}
    root, package, features, owner = selection.get(args.function, ('crate::verifier::candidate::'+args.function, 'crates/aspis-r1-cost-probe', FEATURES, 'aspis_r1_cost_probe'))
    spec = json.loads(Path(args.opacity).read_text())
    opacity = spec[args.function]
    assert all(x['path'].startswith(('crate::','aspis_core::')) and x['why'] for x in opacity)
    cmd = [str(TOOLROOT/'charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or','--start-from',root]
    for x in opacity: cmd += ['--opaque',x.get('selector',x['path'])]
    if args.function in ['entry','process','auth','lane','registry']:cmd += ['--opaque','solana_account_info::AccountInfo']
    for ty in spec['include_types']: cmd += ['--include',ty]
    llbc = out/(args.function+'.llbc')
    cmd += ['--dest-file',str(llbc),'--','--manifest-path',str(workspace/package/'Cargo.toml'),'--locked','--offline','--release','--lib','--jobs','1','--features',features]
    aeneas = [str(TOOLROOT/'aeneas-b59d5188-extended'),'-diagnose-translation','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',('NMX_'+args.function if args.function in ['entry','process','auth','lane','registry'] else 'NMX_'+args.function),'-dest',str(out/'raw'),'-subdir',('NMX_'+args.function if args.function in ['entry','process','auth','lane','registry'] else 'NMX_'+args.function),'-split-files',str(llbc)]
    return dict(charon_command=cmd,aeneas_command=aeneas,opacity=opacity,root=root,root_owner=owner,root_package=package,root_features=features)

def extract(args, workspace, out):
    manifest = validate(workspace,out,args.cargo,args.function)
    pins = options(args,workspace,out)
    for name,h in PINS.items(): assert sha((TOOLROOT/name).read_bytes())==h
    pins.update(frozen_revision=REV,tools=PINS,lock_before=sha((workspace/'Cargo.lock').read_bytes()),manifest_sha256=sha((E/'NMX_STAGING_MANIFEST.json').read_bytes()),candidate_sha256=sha((workspace/'crates/aspis-r1-cost-probe/src/candidate.rs').read_bytes()))
    env = dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(E/'NMX_NHR_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
    write(out/'NMX_PINS.json',pins); print(json.dumps(pins),flush=True)
    try:
        r = subprocess.run(pins['charon_command'],cwd=workspace,env=env); pins['charon_exit']=r.returncode
        if r.returncode==0:
            llbc = out/(args.function+'.llbc'); pins['llbc_sha256']=sha(llbc.read_bytes())
            # Retain complete declarations and their opacity, before Aeneas starts.
            doc = json.loads(llbc.read_text())
            decls = doc.get('translated',doc).get('fun_decls',[])
            inventory = []
            for f in decls:
                if f is None: continue
                meta = f['item_meta']; name = meta['name']
                ids = [x['Ident'][0] for x in name if 'Ident' in x]
                inventory.append(dict(id=f['def_id'],name=name,span=meta['span'],opacity=meta.get('opacity'),body_kind=list(f['body']) if isinstance(f['body'],dict) else f['body'],source_sha256=sha((meta.get('source_text') or '').encode())))
            write(out/'NMX_DECLARATIONS.json',inventory)
            assert not doc['has_errors'], 'Charon reported translation errors'
            # Check each direct native boundary on the actual declaration inventory.
            # Wildcard impl selectors can match several methods: retain ALL matches.
            matched = []
            for boundary in pins['opacity']:
                selector = boundary.get('selector',boundary['path']).replace('crate::',pins['root_owner']+'::')
                parts = selector.split('::')
                hits = []
                for f in inventory:
                    elems = [x['Ident'][0] if 'Ident' in x else '_' for x in f['name']]
                    if len(parts)==len(elems) and all(p=='_' or p==e for p,e in zip(parts,elems)):
                        hits.append(f)
                assert hits, ('OWN INPUT: unmatched opacity',boundary)
                assert all(f['body_kind'] in ('Opaque',['Opaque']) for f in hits), ('OWN INPUT: body not opaque',boundary,hits)
                matched.append(dict(boundary=boundary,matches=hits))
            pins['validated_opacity']=matched
            if args.function in ['entry','process']:
                types=doc.get('translated',doc).get('type_decls',[])
                hits=[t for t in types if t is not None and [p['Ident'][0] for p in t['item_meta']['name'] if 'Ident' in p]==['solana_account_info','AccountInfo']]
                assert hits,'OWN INPUT: missing AccountInfo declaration'
                assert all(t['kind']=='Opaque' or isinstance(t['kind'],dict) and set(t['kind'])=={'Opaque'} for t in hits),('AccountInfo not opaque',hits)
                pins['validated_account_info_opacity']=hits
            write(out/'NMX_PINS.json',pins)
            r = subprocess.run(pins['aeneas_command'],cwd=E,env=env); pins['aeneas_exit']=r.returncode
        pins['exit']=r.returncode
    finally:
        pins['lock_after']=sha((workspace/'Cargo.lock').read_bytes())
        pins['outputs']={str(p.relative_to(out)):sha(p.read_bytes()) for p in (out/'raw').rglob('*') if p.is_file()}
        write(out/'NMX_PINS.json',pins)
        assert pins['lock_after']==pins['lock_before'], 'STOP extraction lock drift'
        assert all(sha((workspace/p).read_bytes())==info['sha256'] for p,info in manifest['files'].items()), 'STOP source drift'
    return r.returncode

def main():
    p=argparse.ArgumentParser(description=__doc__)
    modes=p.add_mutually_exclusive_group(required=True)
    for name in ['export','check','extract','options']: modes.add_argument('--'+name,action='store_true')
    p.add_argument('--workspace',type=Path,default=E/'NMX_workspace'); p.add_argument('--out',type=Path,default=E/'NMX_preflight')
    p.add_argument('--cargo',default='/home/dombarker/.cargo/bin/cargo'); p.add_argument('--function',choices=['lane','registry','auth','prepare','tx1','tx2_authenticated','tx2_common','error','debug','entry','process']); p.add_argument('--opacity',default=str(E/'NMX_OPACITY.json'))
    a=p.parse_args()
    if a.export: export(); return 0
    a.workspace=a.workspace.resolve(); a.out=a.out.resolve(); a.out.mkdir(parents=True,exist_ok=True)
    if a.check or a.extract:
        rel = next(l.split(':',2)[2].strip().lstrip('/') for l in Path('/proc/self/cgroup').read_text().splitlines() if l.startswith('0:'))
        group = Path('/sys/fs/cgroup')/rel
        assert {n:(group/n).read_text().strip() for n in ('memory.high','memory.max','memory.swap.max','pids.max')} == {'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}, 'Run via the admitted capped launcher'
    if a.check: validate(a.workspace,a.out,a.cargo,a.function); return 0
    assert a.function, '--function required'
    if a.options: write(a.out/'NMX_OPTIONS.json',options(a,a.workspace,a.out)); return 0
    return extract(a,a.workspace,a.out)
if __name__=='__main__': sys.exit(main())
