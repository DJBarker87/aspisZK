"""Extract exact source/merged kernel type payloads for differing serializations."""
import pathlib,json,lzma,sys
V=pathlib.Path('/home/dombarker/project-offloads/codex-pv-lib-slice-20261107/v1-coherence');E=V/'evidence';x=json.load(sys.stdin);owners=json.loads(lzma.decompress((E/'ROOT_IMPORT_PREFLIGHT.json.xz').read_bytes()))['root_providers'];comparisons=json.load(open(E/'STATEMENT_COMPARISONS-56563.json'));merged={}
for part in json.load(open(E/'MERGED_TYPE_BATCHES-56560.json')):
 for line in pathlib.Path(part['log']).read_text().splitlines():
  if line.startswith('{'):
   q=json.loads(line);merged[q['root']]=q
pairs=[]
for c in comparisons:
 if not c['differences']:continue
 rows={q['root']:q for q in (json.loads(l) for l in pathlib.Path(c['source']['log']).read_text().splitlines() if l.startswith('{'))}
 for root in c['differences']:
  owner=owners[root];candidates=[owner]+[m for m,o in x['aliases'].items() if o==owner];dest=V/'snapshot-authorities'/c['group'];paths=[str(dest/(m+'.olean')) for m in candidates if (dest/(m+'.olean')).exists()];assert paths,(root,owner)
  pairs.append(dict(root=root,group=c['group'],source_type=rows[root]['type'],merged_type=merged[root]['type'],source_paths=paths,merged_path=str(V/'objects-canonical'/(owner+'.olean'))))
(V/'TYPE_PAIRS.json').write_text(json.dumps(pairs));(E/'TYPE_SERIALIZATION_DIFFERENCES.json.xz').write_bytes(lzma.compress(json.dumps(pairs).encode()));print('Exact differing type pairs',len(pairs))
