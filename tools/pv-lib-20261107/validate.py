"""Evidence integrity checks; never changes a ledger or a proof checker."""
import collections,hashlib,json,lzma,pathlib,re,subprocess
E=pathlib.Path('evidence/pv-lib-20261107')
sha=lambda b:hashlib.sha256(b).hexdigest()
freeze=json.loads((E/'FREEZE.json').read_text())
assert all(sha((E/p).read_bytes())==h for p,h in freeze['files'].items())
assert len(list(E.glob('PSPEC_slice_*.md')))+len(list(E.glob('PSPEC_thread_*.md')))==29
for p in E.glob('PSPEC_*_*.md'):
    assert '## Rejection example' in p.read_text()
for r in json.loads((E/'INPUT_MANIFEST.json').read_text()):
    assert sha(lzma.decompress((E/r['archive']).read_bytes()))==r['sha256']
deps=json.loads((E/'DEPENDENCIES.json').read_text());assert not deps['cycles']
m=json.loads((E/'PLIB_MAP.json').read_text());assert len(m['slots'])==170
instances=json.loads((E/'INSTANCES.json').read_text())
assert len(instances)==83 and all(f['compiled'] and f['raw_audited'] for f in instances.values())
for s in m['slots']:
    if s['root']:assert s['provider_status']=='CLOSED'
    if s['status']=='INSTANTIATED':assert s['instance']['compiled'] and s['instance']['raw_audited']
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('receipt-*.json'))]
accepted={r['target']:r for r in receipts if r['accepted'] and not r['runtime_audit']}
sources=[]
for p in sorted(pathlib.Path('lean').glob('PV_LIB_*.lean')):
    r=accepted.get(p.stem)
    assert r and sha(p.read_bytes())==r['source_sha256'],('uncompiled/changed',p)
    sources.append(dict(path=str(p),sha256=sha(p.read_bytes()),attempt=r['attempt'],
        git_blob=subprocess.check_output(['git','hash-object',str(p)],text=True).strip()))
for r in receipts:
    cmd=r['command']
    for cap in ['MemoryHigh=6G','MemoryMax=8G','MemorySwapMax=0','TasksMax=64']:
        assert cap in cmd
    if r['accepted']:
        assert r['exit']=='0' and r['swaps']=='0'
        assert all('sorryAx' not in a for a in r['axioms_summary_based'])
results=dict(specifications=29,slots=len(m['slots']),slot_status=m['counts'],
    accepted_attempts=sum(r['accepted'] for r in receipts),
    failed_attempts=[r['attempt'] for r in receipts if not r['accepted']],
    refusals=[int(p.stem.split('-')[-1]) for p in E.glob('refusal-*.json')],
    active_sources=sources,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
    source_revision_qualification='Compile-parent HEAD plus exact source SHA/index blob; final source manifest records every accepted byte sequence.',
    formal_results=[{k:r.get(k) for k in ['attempt','target','runtime_audit','accepted','exit','wall',
      'peak_rss_kbytes','swaps','source_revision','source_sha256','axioms_summary_based']} for r in receipts])
raw_audit=json.loads((E/'RAW_AUDIT.json').read_text())
assert raw_audit['strict_raw'] and raw_audit['unresolved']==0 and raw_audit['summary_mismatches']==0
assert raw_audit['root_count']==38
results['strict_raw_audit']={k:raw_audit[k] for k in ['attempt','root_count','unresolved','summary_mismatches']}
session2=json.loads((E/'SESSION2_RAW_AUDIT.json').read_text())
roots=json.loads((E/'SESSION2_AUDIT_ROOTS.json').read_text())
assert session2['strict_raw'] and session2['unresolved']==0 and session2['summary_mismatches']==0
assert session2['root_count']==82 and {r['root'] for r in session2['roots']}==set(roots['roots'])
assert all(r['equal'] and set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'} for r in session2['roots'])
suffix=lambda p:pathlib.Path(p).read_text().split('  let env ← importModules',1)[1]
assert suffix('lean/PV_LIB_RawAudit.lean')==suffix('lean/PV_LIB_RawAudit2.lean')
archive=(E/'SESSION2_RAW_GRAPH_ARCHIVE.json.xz').read_bytes()
manifest=json.loads((E/'SESSION2_RAW_GRAPH_MANIFEST.json').read_text())
assert sha(archive)==manifest['archive_sha256']
payload=lzma.decompress(archive)
assert sha(payload)==manifest['uncompressed_sha256']
contents=json.loads(payload)
assert len(contents)==len(manifest['files'])
for f in manifest['files']:
    b=contents[f['name']].encode()
    assert len(b)==f['bytes'] and sha(b)==f['sha256']
replays=[]
for r in receipts:
    if not (49326<=r['attempt']<=49479 and r['accepted']) or r['target'].startswith('PV_LIB_'):continue
    if r['attempt']<=49385:rev='fc0340264851248e164a098c170cc53e22857085'
    elif r['attempt']<=49448:rev='9d7395cb069f07f812e8e1352e0478111eaec9ee'
    else:rev='ce2f78097fa7e3cabc7b66fdfb9445c067917831'
    raw=subprocess.check_output(['git','show',rev+':lean/'+r['target']+'.lean'])
    assert sha(raw)==r['source_sha256']==sha(pathlib.Path('lean',r['target']+'.lean').read_bytes())
    replays.append(dict(module=r['target'],attempt=r['attempt'],revision=rev,source_sha256=sha(raw)))
assert len(replays)==85
results['session2_unchanged_provider_replays']=replays
results['session2_strict_raw_audit']={k:session2[k] for k in ['attempt','root_count','unresolved','summary_mismatches']}
assert all(p.stat().st_size<20_000_000 for p in E.rglob('*') if p.is_file())
(E/'VALIDATION.json').write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps({k:v for k,v in results.items() if k not in ['active_sources','formal_results','session2_unchanged_provider_replays']},indent=2))
