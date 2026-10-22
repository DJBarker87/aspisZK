#!/usr/bin/env python3
"""Reconcile pass-one records with hash-pinned module MIR and LLVM evidence.

Generic declaration-level corroboration is never instance equality or a
source-to-SBF proof. The release gate fails while any such residual remains.
"""
import argparse,collections,hashlib,importlib.util,json,posixpath,re,resource,subprocess,sys,time
from pathlib import Path
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
OLD=B/'evidence/s10-inventory-20261021';E=B/'evidence/s10-inventory2-20261021'
sha=lambda b:hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
def encoded(x):return (json.dumps(x,indent=2,sort_keys=True)+'\n').encode()
def leaf(n):
    n=re.sub(r'::Instantiated#[0-9a-f]+','',n)
    return n.split('::')[-1]
def span(s):
    m=re.match(r'(.+):(\d+):(\d+): (\d+):(\d+)',s)
    assert m,s
    return posixpath.normpath(m[1]),int(m[2]),int(m[3])-1
def elf_name(n):
    for a,b in [('$LT$','<'),('$GT$','>'),('$u20$',' '),('$RF$','&'),('$u5b$','['),('$u5d$',']'),('$LP$','('),('$RP$',')'),('$C$',',')]:n=n.replace(a,b)
    n=n.replace('..','::');n=re.sub(r'::h[0-9a-f]{16}$','',n)
    return n[1:] if n.startswith('_<') else n
def pathkey(n):
    n=elf_name(n)
    m=re.match(r'^(aspis_\w+)::<(.+)>((?:::).+)$',n)
    if m:
        crate,inner,suffix=m.groups()
        if not inner.startswith((crate+'::','core::','alloc::','std::','&','[')):
            inner=crate+'::'+inner
        inner=re.sub(r' as (?!aspis_|core::|alloc::|std::)([A-Za-z_]\w*::)',r' as '+crate+r'::\1',inner)
        n='<'+inner+'>'+suffix
    return n
def build(census_path):
    old=load(OLD/'inventory.json');manifest=load(E/'probe-manifest.json')
    raw=census_path.read_bytes();assert sha(raw)==manifest['artifacts'][0]['sha256'];assert len(raw)==manifest['artifacts'][0]['bytes']
    census=json.loads(raw);byname={};byline=collections.defaultdict(list);bycol=collections.defaultdict(list)
    for probe in census['probes']:
        for row in probe['declarations']:
            name=row['name'];assert name not in byname,(probe['name'],name)
            byname[name]=dict(row,probe=probe['name']);file,line,col=span(row['span'])
            byline[file,line,leaf(name)].append(name);bycol[file,line,col].append(name)
    keys=collections.defaultdict(list)
    for name in byname:keys[pathkey(name)].append(name)
    identities=load(E/'stage2-identities.json');assert identities['input']['sha256']==load(OLD/'stage2-llbc.json')['input']['sha256']
    canonical={r['id']:r['canonical_name'] for r in identities['declarations']}
    graphs={p:load(OLD/p) for p in ['stage2-llbc.json','verifier-mono-v2.json','verifier-solana-cfg-v3.json']}
    matches={};source_rows={};body_matches=[]
    for graph,g in graphs.items():
        for f in g['declarations']:
            ident=f'llbc:{graph}:{f["id"]}';source_rows[ident]=f
            file=posixpath.normpath(f.get('source_pin',{}).get('path','') or f.get('file',{}).get('Local',''))
            begin=f['span']['beg'];candidates=byline.get((file,begin['line'],leaf(f['name'])),[])
            if not candidates:candidates=bycol.get((file,begin['line'],begin['col']),[])
            # A unique span alone is insufficient for generated macro/drop names.
            candidates=[n for n in candidates if leaf(n)==leaf(f['name']) or
                (leaf(f['name'])=='closure' and 'closure#' in n)]
            method='frozen source file, declaration line and method'
            if graph=='stage2-llbc.json' and canonical[f['id']]:
                structural=keys.get(pathkey(canonical[f['id']]),[])
                structural=[n for n in structural if span(byname[n]['span'])[0]==file]
                if len(structural)==1:
                    candidates=structural;method='structurally expanded LLBC Self type/trait/method + frozen source file'
            if len(candidates)==1:
                matches[ident]=candidates[0]
                body_matches.append(dict(id=ident,mir_name=candidates[0],span=byname[candidates[0]]['span'],
                    matching_method=method,scope='generic declaration only, not monomorphized instance equality'))
    # Cross-check direct LLBC call endpoints against independent rustc MIR.
    checked_edges=[];unmatched_edges=collections.Counter()
    for graph,g in graphs.items():
        for f in g['declarations']:
            caller=f'llbc:{graph}:{f["id"]}'
            if caller not in matches:continue
            mir=byname[matches[caller]]
            targets={c['target'] for c in mir['calls']}
            for i,c in enumerate(f['calls']):
                if c['target'] is None:continue
                target=f'llbc:{graph}:{c["target"]}'
                if target in matches and matches[target] in targets:
                    checked_edges.append(dict(graph=graph,caller=f['id'],call_index=i,target=c['target'],
                        mir_caller=matches[caller],mir_target=matches[target],
                        scope='rustc MIR + Charon agree at declaration endpoints; generic arguments retained in census, specialization equality not inferred'))
                else:unmatched_edges[graph]+=1
    spec=importlib.util.spec_from_file_location('firstpass',R/'tools/s10-inventory-20261021/inventory.py');inv=importlib.util.module_from_spec(spec);spec.loader.exec_module(inv)
    rows={r['id']:r for r in old['declarations']};assignments=[]
    allowed={'lazy_static','digest','curve25519_dalek','block_buffer','generic_array','sha2','subtle','typenum','base64'}
    g=graphs['verifier-mono-v2.json'];parents=collections.defaultdict(list)
    for f in g['declarations']:
        for c in f['calls']:
            if c['target'] is not None:parents[c['target']].append(f['id'])
    # Retain every incoming edge for the native dependencies, including edges
    # from core generic conversion wrappers; no whole native subtree is trusted.
    for ident in old['unassigned']:
        row=rows[ident]
        if ident=='llbc:stage2-llbc.json:154':
            owner='ordered caller join';reason='Compiler tuple drop glue attributed to crate lib.rs; caller composition must retain drop effects.';incoming=[]
        else:
            assert row['evidence']=='verifier-mono-v2.json' and row['name'].split('::')[0] in allowed,ident
            owner='Pool caller';reason='Native diagnostic dependency crate for SDK pubkey/hash/log helpers; emitted candidates include drops/address-taken/unreachable instances. Owned source obligation, not added trust or claimed runtime reachability. Native-to-SBF cfg exclusion remains open.'
            number=int(ident.rsplit(':',1)[1]);incoming=[f'llbc:verifier-mono-v2.json:{i}' for i in parents[number]]
        assignments.append(dict(id=ident,name=row['name'],source_path=row['source_path'],owner=owner,reason=reason,incoming_callers=incoming,status='PROPOSED: owner acceptance required'))
    assert len(assignments)==234
    owner_for={r['id']:r['owner'] for r in assignments}
    remaining=set(old['unassigned'])-set(owner_for)
    multiply_assigned=[ident for ident,n in collections.Counter(r['id'] for r in assignments).items() if n!=1]
    assert not (set(owner_for)-set(old['unassigned']))
    counts=collections.Counter(o for r in old['declarations'] for o in r['owners'])
    counts.update(owner_for.values())
    newowners=[];new_unassigned=[]
    for name,row in byname.items():
        file=span(row['span'])[0];owners,boundary=inv.proposal(name,file)
        if name.startswith('aspis_core::<field::') and file=='crates/aspis-core/src/r0/scalar.rs':
            owners,boundary=['S5'],None # macro-generated CodeField implementations
        if not owners and not boundary and file.startswith(('crates/','programs/')):
            owners=['ordered caller join'] # crate-level drop/derive/constant glue
        if len(owners)+int(boundary is not None)!=1:new_unassigned.append(name)
        newowners.append(dict(name=name,span=row['span'],owner=owners[0] if owners else None,
            boundary=boundary['kind'] if boundary else None,probe=row['probe'],status='diagnostic source candidate; reachability and owner acceptance pending'))
    mir_owner={r['name']:r['owner'] for r in newowners}
    reassignments=[]
    for ident,name in matches.items():
        previous=rows[ident]['owners'];owner=mir_owner[name]
        if len(previous)==1 and owner is not None and previous!=[owner]:
            reassignments.append(dict(id=ident,previous_owner=previous[0],owner=owner,mir_name=name,
                reason='Resolved source type/method identity refines first-pass anonymous implementation-name policy; proposal needs affected owner acceptance.'))
            owner_for[ident]=owner
    counts=collections.Counter(o for r in old['declarations'] for o in ([owner_for[r['id']]] if r['id'] in owner_for else r['owners']))
    # Match only exact demangled paths, allowing crate-local qualification.
    elf_matches=[];elf_unmatched=[]
    for r in old['declarations']:
        if r['evidence']!='linked symbol':continue
        candidates=keys.get(pathkey(r['name']),[])
        if len(candidates)==1:
            elf_matches.append(dict(id=r['id'],symbol=r['name'],raw_symbol_aliases=r['raw_symbol_aliases'],mir_name=candidates[0],span=byname[candidates[0]]['span'],
                resolution='exact demangled path; ELF instance hash retained; no equality of native/SBF generic substitutions or inline expansion asserted'))
        else:elf_unmatched.append(dict(id=r['id'],name=r['name'],reason='External/library/synthetic symbol or no unique exact demangled MIR path; path-erasure heuristics are not accepted as instance proof'))
    dispositions=[]
    unresolved_sites=[]
    trait_summaries={}
    for graph,g in graphs.items():
        if graph=='stage2-llbc.json':
            calls=[dict(caller=f['id'],call_index=i,target=None,trait_kind='GenericOrDynamic',status='Generic H/closure trait clause or observer pointer; needs concrete caller instantiation') for f in g['declarations'] for i,c in enumerate(f['calls']) if c['kind']=='indirect_or_trait']
        else:
            artifact=load(E/('trait-edges-'+graph));assert artifact['input']==g['input']
            calls=artifact['calls'];trait_summaries[graph]=artifact['counts']
        byid={f['id']:f for f in g['declarations']}
        for c in calls:
            f=byid[c['caller']]
            unresolved_sites.append(dict(id=f'llbc:{graph}:{c["caller"]}:call:{c["call_index"]}',
                caller_name=f['name'],source=f['file'],reason=c['status'],metadata=c))
    for mode,g in load(E/'elf-crosscheck.json')['artifacts'].items():
        for c in g['indirect_sites']:
            unresolved_sites.append(dict(id=f'elf:{mode}:callx:{c["address"]:x}',caller_names=c['caller_symbols'],address=c['address'],reason=c['reason']))
    for i,gap in enumerate(old['gaps']):
        d=dict(index=i,original=gap,status='OPEN',reason='Retained original semantic/correspondence frontier; alternative graphs do not prove its discharge.')
        if gap['kind']=='missing_or_opaque_body':
            row=rows[gap['id']];d.update(name=row['name'],source_path=row['source_path'])
            if row['trusted_boundary']:
                d.update(status='BOUNDARY_ACCOUNTED',reason='Declaration explicitly inventoried under existing '+row['trusted_boundary']['kind']+' specification. Backend semantics, callbacks and caller safety remain proof residuals; no body silently invented.')
            elif gap['id'] in matches and byname[matches[gap['id']]]['body_pins']:
                d.update(status='BODY_LOCATED_INSTANCE_OPEN',mir_name=matches[gap['id']],reason='Independent rustc body available for the frozen generic source declaration. Exact retained LLBC specialization and deployed instance correspondence remain open.')
            elif gap['id'] in matches and byname[matches[gap['id']]].get('constant_kind'):
                d.update(status='CONSTANT_DECLARATION_LOCATED',mir_name=matches[gap['id']],reason='rustc identifies this as a compile-time constant, not an executable function body. Value/CTFE correctness and deployed correspondence are not inferred from its name.')
        elif gap['kind']=='extraction_failed_or_stopped':
            d.update(status='HISTORICAL_FAILURE',reason='Original failed/stopped extraction retained. Alternative module MIR succeeds, but does not convert this attempt into successful Charon extraction.')
        dispositions.append(d)
    sowners={'S1','S2','S3','S4','S5','S6','S9'}
    acceptance=[dict(id=r['id'],name=r['name'],owner=owner_for.get(r['id'],r['owners'][0]),source_path=r.get('source_path'),status='pending acceptance; no owner module edited') for r in old['declarations'] if len(r['owners'])==1 and owner_for.get(r['id'],r['owners'][0]) in sowners]
    acceptance += [dict(id='mir:'+r['name'],name=r['name'],owner=r['owner'],source_path=span(r['span'])[0],status='pending acceptance; new diagnostic source candidate, not a reachable-instance claim') for r in newowners if r['owner'] in sowners]
    summary=dict(schema='s10-pass2-reconciliation-v1',source_revision=old['source_revision'],status='INCOMPLETE',
        base_inventory_sha256=sha((OLD/'inventory.json').read_bytes()),census=manifest['artifacts'][0],
        counts=dict(base_records=len(rows),base_unassigned=len(remaining),assigned_twice=old['counts']['assigned_twice']+len(multiply_assigned),
            new_mir_candidates=len(byname),new_mir_unassigned=len(new_unassigned),proposed_base_owners=dict(counts),
            declaration_matches=len(body_matches),ownership_reassignments=len(reassignments),corroborated_LLBC_MIR_edges=len(checked_edges),
            unmatched_LLBC_edges_from_matched_callers=dict(unmatched_edges),elf_path_matches=len(elf_matches),
            elf_path_unmatched=len(elf_unmatched),original_frontiers=len(dispositions),frontier_dispositions=dict(collections.Counter(d['status'] for d in dispositions))),
        retained_trait_inspection=trait_summaries,
        unassigned=sorted(remaining)+new_unassigned,assignments=assignments,ownership_reassignments=reassignments,
        limitations=['Generic source call endpoints corroborated; exact generic substitutions and native/SBF cfg/toolchain transport remain unproved.',
            'No DWARF inline map in frozen ELFs. Native MIR inline scopes are not deployed inline-instance correspondence.',
            'All 152 indirect ELF sites named in elf-crosscheck.json remain target-flow obligations.',
            'Owner acceptance, concrete frozen Calls tree, caller ordering and AcceptedRunJoin remain open.'],
        input_hashes={str(p.relative_to(R)):sha(p.read_bytes()) for p in [OLD/'inventory.json',E/'probe-manifest.json',E/'elf-crosscheck.json',E/'source-recheck.json',E/'stage2-identities.json',E/'trait-edges-verifier-mono-v2.json',E/'trait-edges-verifier-solana-cfg-v3.json']})
    return {'reconciliation.json':summary,'body-matches.json':body_matches,'corroborated-edges.json':checked_edges,
        'elf-source-paths.json':dict(matched=elf_matches,unmatched=elf_unmatched),
        'frontier-dispositions.json':dispositions,'owner-acceptance.json':acceptance,
        'mir-owners.json':newowners,'unresolved-sites.json':unresolved_sites}
def main():
    a=argparse.ArgumentParser();a.add_argument('--census',type=Path,default=Path('/tmp/cx-s10-inventory2-analysis/mir-census.json'));a.add_argument('--check',action='store_true');a.add_argument('--require-complete',action='store_true');args=a.parse_args()
    start=time.monotonic();outputs=build(args.census)
    for name,value in outputs.items():
        raw=encoded(value);assert len(raw)<=5_000_000,(name,len(raw))
        if args.check:assert (E/name).read_bytes()==raw,'stale '+name
        else:(E/name).write_bytes(raw)
    result=outputs['reconciliation.json'];status=2 if args.require_complete and result['status']!='COMPLETE' else 0
    print(json.dumps(dict(status=result['status'],exit_status=status,counts=result['counts']),sort_keys=True))
    if not args.check:
        usage=resource.getrusage(resource.RUSAGE_SELF)
        receipt=dict(target='tools/s10-inventory2-20261021/reconcile.py',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
            generator_sha256=sha(Path(__file__).read_bytes()),exit_status=status,wall_seconds=time.monotonic()-start,
            peak_rss_bytes=usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024,swaps=usage.ru_nswap,
            print_axioms='N/A: no new Lean theorem. Existing four standard-axiom model audits reused; no source completeness proof.',
            output_hashes={k:sha(encoded(v)) for k,v in outputs.items()})
        (E/'reconcile-receipt.json').write_bytes(encoded(receipt))
    raise SystemExit(status)
if __name__=='__main__':main()
