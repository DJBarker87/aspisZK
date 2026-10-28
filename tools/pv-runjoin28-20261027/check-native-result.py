from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin28-20261027'
name='pv28-frontier-01';r=json.loads((E/name/'receipt.json').read_text());out=(E/name/'out.log').read_text()
assert r['exit']==0 and r['swaps']==0
assert r['controls']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for p,h in r['source_sha256'].items():assert hashlib.sha256((R/p).read_bytes()).hexdigest()==h,p
expected=['canonical_control=Ok','tree_validation=Ok frontier00=2147483647 index=1','noncanonical_frontier_preparation=Ok retained_frontier00=2147483647','snapshot_codec=Err(NonCanonicalDigest)']
assert all(s in out for s in expected)
pins=json.loads((E/'native-source-check.json').read_text());assert not pins['mismatches'] and pins['expected']==pins['actual']
(E/'native-result.json').write_text(json.dumps(dict(classification='optimized native guard/representation probe; not a Lean execution theorem or RustRealRefinement',receipt=name+'/receipt.json',expected_lines=expected,all_source_files_matched=len(pins['expected']),snapshot_index=1,frontier00=2147483647,compiler_returned_fresh_payload=True,payload_preserves_snapshot=True,codec_rejects_same_snapshot=True,does_not_refute_canonical_encoder_route=True),indent=2)+'\n')
print('Verified fresh successful compiler return with noncanonical active frontier and codec rejection')
