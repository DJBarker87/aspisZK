#!/usr/bin/env python3
"""NPK_ extraction inputs: map every committed prov-p* *_spec.json (research branch) to its Charon cargo
configuration; for frozen-tree configurations attach the host-target file cone (NPK_N011..N015) and
resolve each --start-from path to its module file at 4bb3b3f.  Run from the worktree root after
NPK_analyze.py; adds key 'extraction' to NPK_CONE_FILES.json."""
import json,subprocess,re,collections,pathlib
E=pathlib.Path('evidence/build-cone-20261110'); V='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
git=lambda *a: subprocess.check_output(['git',*a],stderr=subprocess.DEVNULL).decode()
REF='research'; REFSHA=git('rev-parse',REF).strip()
names=[p for p in git('ls-tree','-r','--name-only',REF,'evidence/').split('\n') if re.match(r'evidence/prov-p\d[a-z]*-\d+/[^/]+_spec\.json$',p)]
pco=json.loads(git('show',f'{REF}:evidence/prov-p0-20261109/PCO_extract_specs.json'))
CONF={('crates/aspis-core/Cargo.toml','r0'):'NPK_N011',
      ('crates/aspis-r1-cost-probe/Cargo.toml','private-leaf-salts,optimized-terminal,program-build'):'NPK_N012',
      ('crates/aspis-statement/Cargo.toml','r0,pool-v1-kernel'):'NPK_N013',
      ('crates/aspis-statement/Cargo.toml','r0,pool-v1-kernel,pool-v1-pair-forest-packed-digest-selector-tensor-audit,pool-v1-pair-forest-binary-copy-weights-audit,pool-v1-pair-forest-endpoint-selector-cache-audit,pool-v1-pair-forest-semantic-factor-audit,pool-v1-pair-forest-pattern-window-audit,pool-v1-pair-forest-copy-tag-dot-basis-audit,pool-v1-pair-forest-copy-finish-dot-basis-audit,pool-v1-pair-forest-packed-range-audit,pool-v1-pair-forest-active-mask-basis-audit'):'NPK_N014',
      ('programs/r1-cost-probe/Cargo.toml','pool-adapter,private-leaf-salts'):'NPK_N015'}
ROOT={'aspis_core':'crates/aspis-core/src','aspis_statement':'crates/aspis-statement/src','aspis_r1_cost_probe':'crates/aspis-r1-cost-probe/src','aspis_r1_cost_probe_program':'programs/r1-cost-probe/src'}
MCRATE={'crates/aspis-core/Cargo.toml':'aspis_core','crates/aspis-statement/Cargo.toml':'aspis_statement','crates/aspis-r1-cost-probe/Cargo.toml':'aspis_r1_cost_probe','programs/r1-cost-probe/Cargo.toml':'aspis_r1_cost_probe_program'}
tracked=set(git('ls-tree','-r','--name-only',V,'crates','programs/r1-cost-probe').split())
def resolve(path,crate):
    parts=path.split('::')
    if parts[0]=='crate': base=ROOT[crate]; parts=parts[1:]
    elif parts[0] in ROOT: base=ROOT[parts[0]]; parts=parts[1:]
    else: return '<library root, no repository file: %s>'%parts[0]
    best=base+('/lib.rs')
    cur=base
    for i,p in enumerate(parts):
        if p=='_' : break
        for cand in (f'{cur}/{p}.rs',f'{cur}/{p}/mod.rs'):
            if cand in tracked: best=cand
        if f'{cur}/{p}.rs' in tracked or f'{cur}/{p}/mod.rs' in tracked: cur=f'{cur}/{p}'
        else: break
    return best
cone=json.loads((E/'NPK_CONE_FILES.json').read_text())
vc=set(cone['sets']['verifier_cone'])
runs=[]; byconf=collections.defaultdict(list); nonfrozen=[]
for n in names:
    d=json.loads(git('show',f'{REF}:{n}')); c=d.get('charon_command')
    if isinstance(c,str): c=c.split()
    rec=dict(spec_file=n,run=d.get('run'),spec_id=d.get('spec_id'))
    if not c or '--' not in c:
        rec['config']='non-cargo (prebuilt LLBC or tool build)'; nonfrozen.append(rec); continue
    i=c.index('--'); post=c[i+1:]
    mp=post[post.index('--manifest-path')+1] if '--manifest-path' in post else None
    feats=post[post.index('--features')+1] if '--features' in post else ''
    rel=re.sub(r'^.*?/(crates|programs)/',r'\1/',mp) if mp else None
    frozen_ws = mp and ('{WS}' in mp or re.search(r'/(PCO|PCQ[A-Z]?|PCR[A-Z]?|PCS[A-Z]?)_?workspace/',mp) or re.search(r'_workspace/',mp))
    key=(rel,feats)
    sf=[c[k+1] for k,a in enumerate(c[:i]) if a=='--start-from']
    rec.update(manifest=mp,features=feats,start_from=sf)
    if key in CONF and frozen_ws:
        rec['config']=CONF[key]; crate=MCRATE[rel]
        rec['start_from_files']={s:resolve(s,crate) for s in sf}
        byconf[CONF[key]].append(rec)
    else:
        rec['config']='non-frozen crate (own uploaded/archived sources)'; nonfrozen.append(rec)
    runs.append(rec)
sffiles=collections.defaultdict(set)
for k,rs in byconf.items():
    for r in rs:
        for s,f in r['start_from_files'].items(): sffiles[f].add(r['run'])
pco_ids={s['spec_id']:s for s in pco['specs']}
out=dict(source_ref=f'{REF} {REFSHA}',n_spec_files=len(names),
  configs={k:dict(cone=k,n_runs=len(v),runs=sorted({r['run'] for r in v}),spec_ids=sorted({str(r['spec_id']) for r in v}),
                  files_not_in_verifier_cone=sorted(r['path'] for r in cone['native'][k]['files'] if not r['in_verifier_cone'])) for k,v in sorted(byconf.items())},
  start_from_files={f:dict(runs=sorted(v),in_verifier_cone=f in vc) for f,v in sorted(sffiles.items(),key=lambda x:str(x[0]))},
  non_frozen=[dict(run=r['run'],spec_file=r['spec_file'],config=r['config'],manifest=r.get('manifest')) for r in nonfrozen],
  pco_gate_specs={sid:dict(kind=s['kind'],manifest=s.get('manifest'),features=s.get('features'),retired=bool(s.get('retired')),
        config=CONF.get((s.get('manifest'),s.get('features'))) if s['kind'].startswith('frozen') else None) for sid,s in pco_ids.items()})
cone['extraction']=out
(E/'NPK_CONE_FILES.json').write_text(json.dumps(cone,indent=1)+'\n')
print(len(names),'spec files;',{k:len(v) for k,v in byconf.items()},'non-frozen',len(nonfrozen))
for f,v in out['start_from_files'].items(): print(' ',f,len(v['runs']),'in VC' if v['in_verifier_cone'] else 'NOT in VC')
print('PCO frozen spec configs:',collections.Counter(v['config'] for v in out['pco_gate_specs'].values() if v['kind'].startswith('frozen')))
