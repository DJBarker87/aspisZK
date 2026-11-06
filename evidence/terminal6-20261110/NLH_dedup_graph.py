from pathlib import Path
import hashlib,json,lzma
p=Path(__file__).resolve().parent;files=sorted(p.glob('NLH_K*-graph.json'));assert len(files)==47
raw=files[0].read_bytes();digest=hashlib.sha256(raw).hexdigest();blob=lzma.compress(raw,preset=6);assert lzma.decompress(blob)==raw
canonical=p/'NLH_RESOLVED_GRAPH.json.xz';canonical.write_bytes(blob);(p/'NLH_RESOLVED_GRAPH.json.sha256').write_text(digest+'\n');rows=[]
for q in files:
 data=q.read_bytes();assert data==raw
 a=q.name[:-len('-graph.json')];check=json.loads((p/(a+'-graph-check.json')).read_text());assert check['graph_sha256']==digest and check['graph_matches_frozen']
 ref=dict(original_file=q.name,raw_bytes=len(data),raw_sha256=digest,archive=canonical.name,archive_sha256=hashlib.sha256(blob).hexdigest(),recorded_per_run_validation=a+'-graph-check.json')
 (p/(a+'-graph.ref.json')).write_text(json.dumps(ref,indent=1)+'\n');rows.append(ref)
# Only redundant local evidence payloads are removed; their complete bytes are
# retained once above. Host workspace, caches, targets and TMPDIR are untouched.
for q in files:q.unlink()
(p/'NLH_GRAPH_DEDUP.json').write_text(json.dumps(dict(status='BYTE_IDENTICAL_DEDUPLICATION',raw_sha256=digest,original_payloads=47,original_total_bytes=47*len(raw),retained_archive=canonical.name,retained_archive_bytes=len(blob),rows=rows),indent=1)+'\n');print(json.dumps(dict(graphs=47,unique_payloads=1,raw_sha256=digest,archive_bytes=len(blob))))
