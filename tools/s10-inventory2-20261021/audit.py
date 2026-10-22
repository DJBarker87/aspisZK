#!/usr/bin/env python3
"""Focused integrity and fail-closed checks, including adversarial mutations."""
import copy,hashlib,importlib.util,json,resource,subprocess,sys,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('pass2',HERE/'reconcile.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
start=time.monotonic();checks=[]
def validate(outputs):
    old=m.load(m.OLD/'inventory.json');x=outputs['reconciliation.json'];assign=x['assignments']
    ids=[r['id'] for r in assign]
    assert len(ids)==len(set(ids)) and set(ids)==set(old['unassigned'])
    assert all(r['owner'] in old['owners'] for r in assign)
    assert all('trusted_boundary' not in r for r in assign)
    assert x['counts']['base_unassigned']==len(set(old['unassigned'])-set(ids))
    decls={r['id']:r for r in old['declarations']}
    assert all(len(r['owners'])+int(r['trusted_boundary'] is not None)==1 for r in decls.values() if r['id'] not in ids)
    frontier=outputs['frontier-dispositions.json']
    assert len(frontier)==len(old['gaps']) and [r['index'] for r in frontier]==list(range(len(old['gaps'])))
    assert all(r['original']==old['gaps'][i] and r['reason'] for i,r in enumerate(frontier))
    matched={r['id']:r['mir_name'] for r in outputs['body-matches.json']}
    newowners={r['name']:r['owner'] for r in outputs['mir-owners.json']}
    assert all(int(r['owner'] is not None)+int(r['boundary'] is not None)==1 for r in outputs['mir-owners.json'])
    assert len(newowners)==x['counts']['new_mir_candidates']
    overrides=x['ownership_reassignments'];override_ids=[r['id'] for r in overrides]
    assert len(override_ids)==len(set(override_ids))
    for r in overrides:
        assert decls[r['id']]['owners']==[r['previous_owner']]
        assert matched[r['id']]==r['mir_name'] and newowners[r['mir_name']]==r['owner']
    graphs={name:m.load(m.OLD/name) for name in ['stage2-llbc.json','verifier-mono-v2.json','verifier-solana-cfg-v3.json']}
    for edge in outputs['corroborated-edges.json']:
        byid={r['id']:r for r in graphs[edge['graph']]['declarations']}
        call=byid[edge['caller']]['calls'][edge['call_index']]
        assert call['target']==edge['target']
        assert matched[f'llbc:{edge["graph"]}:{edge["caller"]}']==edge['mir_caller']
        assert matched[f'llbc:{edge["graph"]}:{edge["target"]}']==edge['mir_target']
    assert x['status']=='INCOMPLETE' and x['limitations']
outputs={name:m.load(m.E/name) for name in ['reconciliation.json','body-matches.json','corroborated-edges.json','elf-source-paths.json','frontier-dispositions.json','owner-acceptance.json','mir-owners.json','unresolved-sites.json']}
receipt=m.load(m.E/'reconcile-receipt.json')
assert receipt['generator_sha256']==m.sha((HERE/'reconcile.py').read_bytes())
for name,value in outputs.items():assert receipt['output_hashes'][name]==m.sha(m.encoded(value))
for path,digest in outputs['reconciliation.json']['input_hashes'].items():assert m.sha((m.R/path).read_bytes())==digest
validate(outputs);checks.append('frozen inputs, exact ownership partition, call endpoint IDs, all original frontier dispositions and deterministic output pins')
for kind in ['duplicate_owner','false_edge','hidden_frontier','conflicting_source_owner']:
    bad=copy.deepcopy(outputs)
    if kind=='duplicate_owner':bad['reconciliation.json']['assignments'].append(bad['reconciliation.json']['assignments'][0])
    elif kind=='false_edge':bad['corroborated-edges.json'][0]['target']=-1
    elif kind=='hidden_frontier':bad['frontier-dispositions.json'].pop()
    else:bad['reconciliation.json']['ownership_reassignments'][0]['owner']='S10'
    try:validate(bad)
    except (AssertionError,KeyError):checks.append('rejects '+kind)
    else:raise AssertionError('mutation accepted: '+kind)
manifest=m.load(m.E/'probe-manifest.json');assert len(manifest['probes'])==28
assert manifest['driver_source']['sha256']==m.sha((HERE/'mir_edges.rs').read_bytes())
source_recheck=m.load(m.E/'source-recheck.json')
assert source_recheck['manifest']['sha256']==m.sha((m.OLD/'source-hashes.json').read_bytes())
assert source_recheck['files']==488 and source_recheck['mismatches']==[]
driver_versions={m.sha(p.read_bytes()) for p in [HERE/'mir_edges.rs',HERE/'historical/mir_edges_v6.rs']}
assert len([r for r in manifest['probes'] if r['name'].startswith('pool-')])==24
success=[]
for probe in manifest['probes']:
    p=m.E/'receipts'/probe['name'];r=m.load(p/'receipt.json');command=m.load(p/'command.json')
    assert r['exit_status']==0 and r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
    assert r['swaps']==0 and r['wall_seconds']<600
    assert command['source_revision']==outputs['reconciliation.json']['source_revision']
    assert command['driver_sha256'] in driver_versions
    assert command['env']['S10_MODULE']!='*' or not probe['name'].startswith('pool-')
    success.append(r)
checks.append('28 successful timed and capped probes; all 24 Pool modules individually selected; zero swap')
elf=m.load(m.E/'elf-crosscheck.json');original=m.load(m.OLD/'elf-graphs.json')
for mode,g in elf['artifacts'].items():
    assert g['linked']==original['artifacts'][mode]['linked'] and g['deployed']==original['artifacts'][mode]['deployed']
    byaddr={c['address']:c for c in original['artifacts'][mode]['calls']}
    assert len(g['calls'])==len(byaddr)
    for c in g['calls']:
        old=byaddr[c['address']];assert c['kind']==old['kind']
        if c['kind']!='indirect':assert c['target']==old['target']
    assert not g['debug_info_present']
checks.append('LLVM call/relocation checks agree with original decoder for every site in all three pinned ELFs')
for name in ['verifier-mono-v2','verifier-solana-cfg-v3']:
    traits=m.load(m.E/f'trait-edges-{name}.json');graph=m.load(m.OLD/(name+'.json'))
    assert traits['input']==graph['input']
    byid={r['id']:r for r in graph['declarations']}
    for c in traits['calls']:
        old=byid[c['caller']]['calls'][c['call_index']]
        assert old['kind']=='indirect_or_trait' and old['function_sha256']==c['function_sha256']
        assert c['target'] is None
    assert len(traits['calls'])==sum(c['kind']=='indirect_or_trait' for f in byid.values() for c in f['calls'])
checks.append('every retained verifier indirect/trait call inspected; absent method-table targets remain absent, not fabricated')
proof=m.load(m.OLD/'OraclePortS10ModelInventory-7/receipt.json')
assert proof['exit_status']==0 and proof['source_sha256']==m.sha((m.B/'lean/OraclePortS10ModelInventory.lean').read_bytes())
assert len(proof['print_axioms'])==4
assert all(line.endswith('depends on axioms: [propext, Classical.choice, Quot.sound]') for line in proof['print_axioms'])
checks.append('unchanged model source and four standard-axiom audits reused; no new Lean claim')
gate=subprocess.run([sys.executable,'-B',str(HERE/'reconcile.py'),'--check','--require-complete'],text=True,capture_output=True)
assert gate.returncode==2,gate.stdout+gate.stderr
checks.append('regeneration agrees byte for byte; incomplete release gate exits 2')
assert all(p.stat().st_size<=5_000_000 for p in m.E.rglob('*.json'))
assert manifest['artifacts'][0]['bytes']>5_000_000 and manifest['artifacts'][0]['generator']
checks.append('large derived census represented by SHA-256, byte size and generator only')
usage=resource.getrusage(resource.RUSAGE_SELF)
result=dict(schema='s10-pass2-integrity-receipt-v1',target='tools/s10-inventory2-20261021/audit.py',
    source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=m.R,text=True).strip(),source_sha256=m.sha(Path(__file__).read_bytes()),exit_status=0,
    wall_seconds=time.monotonic()-start,peak_rss_bytes=usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024,swaps=usage.ru_nswap,
    print_axioms=proof['print_axioms'],axioms_scope='Reused first-pass model-only theorem; no new proof or source-completeness claim',checks=checks,
    completeness_gate=dict(exit_status=gate.returncode,stdout=gate.stdout,stderr=gate.stderr),
    focused_probe_max_wall_seconds=max(r['wall_seconds'] for r in success),focused_probe_max_peak_rss_kib=max(r['peak_rss_kib'] for r in success),
    evidence_output_hashes={name:m.sha(m.encoded(value)) for name,value in outputs.items()})
(m.E/'validation.json').write_bytes(m.encoded(result));print(json.dumps(dict(exit_status=0,checks=len(checks),completeness_gate=gate.returncode,wall_seconds=result['wall_seconds'])))
