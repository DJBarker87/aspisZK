#!/usr/bin/env python3
"""NPK_ analysis: per-ELF and per-extraction-config in-repository file cones from the host dep-info
collections (host/analysis/*_cone.json), checked against git blobs at the pins; prover-cfg scan of
every cone file; free change set.  Run from the repository root of the worktree:
  python3 -I evidence/build-cone-20261110/NPK_analyze.py
Writes evidence/build-cone-20261110/NPK_CONE_FILES.json and NPK_TABLES.md (fragments)."""
import json,subprocess,hashlib,pathlib,re,sys,collections,importlib.util,posixpath
E=pathlib.Path('evidence/build-cone-20261110'); A=E/'host/analysis'
V='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'; P='b936275465600469312d1f058cdc91ea2a11f3dc'
spec=importlib.util.spec_from_file_location('cfgscan',E/'NPK_cfgscan.py'); cs=importlib.util.module_from_spec(spec); spec.loader.exec_module(cs)
git=lambda *a: subprocess.check_output(['git',*a],stderr=subprocess.DEVNULL)
def blob(rev,p):
    try: return git('cat-file','blob',f'{rev}:{p}')
    except subprocess.CalledProcessError: return None
def tree(rev,p):
    try: return git('rev-parse',f'{rev}:{p}').decode().strip()
    except subprocess.CalledProcessError: return None
sha=lambda b: hashlib.sha256(b).hexdigest()
def gitblob(b): return hashlib.sha1(b'blob %d\0'%len(b)+b).hexdigest()
CR=['crates/aspis-core','crates/aspis-statement','crates/aspis-r1-cost-probe','crates/aspis-prover','programs/r1-cost-probe','programs/aspis-pool','programs/aspis-verifier','docs/research/v8-r0-zk-20261009/refine/writers','docs/research/v8-r0-zk-20261009/refine/blockwriters','docs/research/v8-r0-zk-20261009/refine/poseidon','docs/research/v8-r0-zk-20261009/refine/diffharness','docs/research/v8-r0-zk-20261009/z4','docs/research/v8-r0-zk-20261009/c3']
CRATE_OF=lambda p: (p.split('/src/')[0] if '/src/' in p else p.rsplit('/',1)[0])
ELFS={'NPK_B001':dict(elf='verifier default',sha='f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4',rev=V,program='programs/r1-cost-probe',features='pool-adapter,private-leaf-salts'),
      'NPK_B003':dict(elf='verifier devnet',sha='63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299',rev=V,program='programs/r1-cost-probe',features='pool-adapter,private-leaf-salts',env='ASPIS_R1_POOL_PROGRAM_ID=BmsNik..., ASPIS_R1_REGISTRY_PROGRAM_ID=9pWwAc...'),
      'NPK_B004':dict(elf='verifier retarget (NPC devnet)',sha='2331ad8a2d97439a30329328c51f619a6b13be97e260ab1e1fd8aab22cb996ea',rev=V,program='programs/r1-cost-probe',features='pool-adapter,private-leaf-salts',env='ASPIS_R1_POOL_PROGRAM_ID=37hdATMk..., ASPIS_R1_REGISTRY_PROGRAM_ID=9pWwAc...'),
      'NPK_B002':dict(elf='Pool',sha='e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc',rev=P,program='programs/aspis-pool',features='r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit')}
NAT={'NPK_N011':('crates/aspis-core/Cargo.toml','r0'),
     'NPK_N012':('crates/aspis-r1-cost-probe/Cargo.toml','private-leaf-salts,optimized-terminal,program-build'),
     'NPK_N013':('crates/aspis-statement/Cargo.toml','r0,pool-v1-kernel'),
     'NPK_N014':('crates/aspis-statement/Cargo.toml','r0,pool-v1-kernel,<9 optimized-terminal audit features>'),
     'NPK_N015':('programs/r1-cost-probe/Cargo.toml','pool-adapter,private-leaf-salts'),
     'NPK_N016':('crates/aspis-r1-cost-probe/Cargo.toml','prover,r1p-check (prover cone, not an extraction config)')}
def load(a):
    d=json.load(open(A/f'{a}_cone.json')); files={}
    for u in d['units']:
        unit=u['depinfo'].split('/')[-1]
        for f in u['files']:
            if f['kind']=='repo': files.setdefault(posixpath.normpath(f['path']),dict(host_sha256=f['sha256'],units=set()))['units'].add(unit)
    return d,files
res=dict(schema=1,job='NPK_',target_established=False,pins=dict(verifier=V,pool=P),elfs={},native={},manifests={})
cone_union=set(); pool_cone=set(); ver_cone=set(); ext_union=set()
mismatch=[]
for a,meta in ELFS.items():
    d,files=load(a); rows=[]
    for p,info in sorted(files.items()):
        b=blob(meta['rev'],p)
        ok = b is not None and sha(b)==info['host_sha256']
        if not ok: mismatch.append((a,p))
        rows.append(dict(path=p,sha256=info['host_sha256'],git_blob=gitblob(b) if b else None,matches_pin=ok,units=sorted(info['units']),crate=next((c for c in CR if p.startswith(c+'/')),'other')))
    feats={c['crate']:c['features'] for c in d['rustc'] if not c['crate'].startswith('build_script')}
    env=[(u['depinfo'].split('/')[-1],u['env_deps']) for u in d['units'] if u['env_deps'] and any(f['kind']=='repo' for f in u['files'])]
    regs=sorted({f['path'].split('/')[2] for u in d['units'] for f in u['files'] if f['kind']=='registry' and f['path'].startswith('src/')})
    res['elfs'][a]=dict(meta,files=rows,n_files=len(rows),crate_features={k:v for k,v in feats.items() if k.startswith('aspis')},
        env_deps=env,registry_packages=regs,prover_feature_on=('prover' in feats.get('aspis_r1_cost_probe',[])))
    s={r['path'] for r in rows}; cone_union|=s
    (pool_cone if a=='NPK_B002' else ver_cone).update(s)
for a,(m,f) in NAT.items():
    d,files=load(a); rows=[]
    for p,info in sorted(files.items()):
        b=blob(V,p); src='4bb3b3f'
        if p.startswith('programs/aspis-pool'): b=blob(P,p); src='b936275'
        ok=b is not None and sha(b)==info['host_sha256']
        if not ok: mismatch.append((a,p))
        rows.append(dict(path=p,sha256=info['host_sha256'],matches_pin=ok,in_verifier_cone=p in ver_cone,in_pool_cone=p in pool_cone))
    feats={c['crate']:c['features'] for c in d['rustc'] if c['crate'].startswith(('aspis','r1'))}
    res['native'][a]=dict(manifest=m,features=f,files=rows,n_files=len(rows),crate_features=feats)
    if a!='NPK_N016': ext_union|={r['path'] for r in rows}
prover_cone={r['path'] for r in res['native']['NPK_N016']['files']}
# manifests and workspace inputs that are not in dep-info but select the build
pk=['Cargo.toml','Cargo.lock','.cargo/config.toml','crates/aspis-core/Cargo.toml','crates/aspis-statement/Cargo.toml',
    'crates/aspis-r1-cost-probe/Cargo.toml','programs/r1-cost-probe/Cargo.toml','programs/aspis-pool/Cargo.toml',
    'docs/research/v8-r0-zk-20261009/refine/writers/Cargo.toml','docs/research/v8-r0-zk-20261009/refine/blockwriters/Cargo.toml',
    'docs/research/v8-r0-zk-20261009/refine/poseidon/Cargo.toml','crates/aspis-prover/Cargo.toml','docs/research/v8-r0-zk-20261009/z4/Cargo.toml']
for p in pk:
    b=blob(V,p); bp=blob(P,p)
    res['manifests'][p]=dict(sha256_4bb3b3f=sha(b) if b else None,sha256_b936275=sha(bp) if bp else None,identical=(b==bp))
# tree hashes
res['trees']={p:{'4bb3b3f':tree(V,p),'b936275':tree(P,p)} for p in ['crates','crates/aspis-core','crates/aspis-statement','crates/aspis-r1-cost-probe','crates/aspis-prover','programs/r1-cost-probe','programs/aspis-pool','docs/research/v8-r0-zk-20261009/refine/writers','docs/research/v8-r0-zk-20261009/refine/blockwriters','docs/research/v8-r0-zk-20261009/refine/poseidon','docs/research/v8-r0-zk-20261009/z4','Cargo.lock','Cargo.toml']}
res['generated']=dict(path='OUT_DIR/circle_tables.rs (aspis-core build.rs)',sha256_sbf='7fbe0464c940393bf8c59e676fd60d8411a296f0260f649fa27bbf9447a96491',note='identical in all four ELF builds; generated by crates/aspis-core/build.rs, which is in the cone')
# cfg scan of every cone/extraction/prover-cone .rs file at the verifier pin (Pool files at b936275)
VFEAT={'default','optimized-terminal','private-leaf-salts','program-build','r0','pool-v1-kernel','pool-adapter','custom-heap'}
scanned={}
for p in sorted(cone_union|ext_union|prover_cone):
    if not p.endswith('.rs'): continue
    b=blob(P if p.startswith('programs/aspis-pool') else V,p).decode('utf-8')
    hits=cs.scan(b,VFEAT)
    if hits: scanned[p]=hits
res['prover_cfg_items']=scanned
union_gate=cone_union|ext_union
res['sets']=dict(verifier_cone=sorted(ver_cone),pool_cone=sorted(pool_cone),extraction_cone=sorted(ext_union),
    extraction_not_in_elf_cones=sorted(ext_union-cone_union),prover_cone=sorted(prover_cone),
    prover_only_free=sorted(prover_cone-union_gate),
    shared_files_with_prover_items=sorted(p for p in scanned if p in union_gate))
# all tracked files under the export roots, classified
listing=git('ls-tree','-r','--name-only',V,'crates','programs/r1-cost-probe','docs/research/v8-r0-zk-20261009/refine/writers','docs/research/v8-r0-zk-20261009/refine/blockwriters','docs/research/v8-r0-zk-20261009/refine/poseidon','docs/research/v8-r0-zk-20261009/z4','docs/research/v8-r0-zk-20261009/c3','docs/research/v8-r0-zk-20261009/refine/diffharness','programs/aspis-verifier').decode().split()
cls=collections.Counter(); free=[]
for p in listing:
    if p in pk: c='manifest'
    elif p in union_gate: c='gated'
    elif p in prover_cone: c='prover_only'
    else: c='not_compiled_in_recorded_configs'
    cls[c]+=1
    if c!='gated' and c!='manifest': free.append(dict(path=p,cls=c))
res['tracked_classification']=dict(counts=dict(cls),free=free)
ps=collections.defaultdict(list)
for l in (A/'NPK_ELF_PATH_STRINGS.txt').read_text().split('\n'):
    if l.strip(): a,pth=l.split(); ps[a].append(pth)
for a in res['elfs']: res['elfs'][a]['source_paths_embedded_in_elf']=sorted(ps[a])
res['pin_mismatches']=mismatch
(E/'NPK_CONE_FILES.json').write_text(json.dumps(res,indent=1,default=sorted)+'\n')
print('mismatches',mismatch)
for a,e in res['elfs'].items(): print(a,e['elf'],e['n_files'],'prover_on=',e['prover_feature_on'])
for a,e in res['native'].items(): print(a,e['manifest'],e['n_files'],'not in verifier cone:',sum(not r['in_verifier_cone'] for r in e['files']))
print('verifier cone',len(ver_cone),'pool cone',len(pool_cone),'union',len(cone_union),'ext',len(ext_union),'ext-only',len(ext_union-cone_union),'prover cone',len(prover_cone),'free prover-only',len(prover_cone-union_gate))
print('tracked',dict(cls))
for p,h in scanned.items(): print(p,'GATED' if p in union_gate else 'free',len(h))
