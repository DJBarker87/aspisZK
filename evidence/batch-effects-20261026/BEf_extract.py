"""Pin verbatim source bodies for a native batch rejection witness.
No source function is replaced, bounded, or simplified by this extractor.
"""
from pathlib import Path
import hashlib,json,sys
base=Path(__file__).resolve().parents[2]
source=base/'crates/aspis-r1-cost-probe/src/candidate.rs'
raw=source.read_text()
names=['opening','slot','batch_keys','sort_batch_keys','batch_leaf','same_batch_leaf','same_batch_index','batch_key_at','batch_merkle_values','batch_tree']
parts=[]; pins={}
for name in names:
    start=raw.index('fn '+name+'<' if name in ['batch_leaf','batch_merkle_values','batch_tree'] else 'fn '+name+'(')
    brace=raw.index('{',start); depth=1;end=brace+1
    while depth:
        depth+=(raw[end]=='{')-(raw[end]=='}');end+=1
    body=raw[start:end]
    parts.append(body)
    pins[name]={'start_line':raw[:start].count('\n')+1,'end_line':raw[:end].count('\n')+1,'sha256':hashlib.sha256(body.encode()).hexdigest()}
tree=parts[-1]
tail=tree[tree.index('    let count ='):tree.rindex('}')].rstrip()
header='fn BEf_source_tail<H: Digest32>(proof: &[u8], root: [u8;32], s: usize, idx: &mut [u32; multiproof::MAX_BATCH], val: &mut [[u8;32]; multiproof::MAX_BATCH], d: usize, hash: H) -> Result<(), Error> {\n'
parts.append(header+tail+'\n}')
gstart=tail.index('    if count > SLOT_NODES[s]')
gbrace=tail.index('{',gstart);gdepth=1;gend=gbrace+1
while gdepth:
    gdepth+=(tail[gend]=='{')-(tail[gend]=='}');gend+=1
guard=tail[gstart:gend]
parts.append('fn BEf_source_padding_guard(nodes: &[u8], s: usize, count: usize) -> Result<(), Error> {\n'+guard+'\n    Ok(())\n}')
pins['BEf_source_padding_guard']={'body_sha256':hashlib.sha256(guard.encode()).hexdigest(),'binding':'Exact source padding condition and Err(Parse) exit; explicit Ok continuation only for the local fragment.'}
pins['BEf_source_tail']={'start_line':raw[:raw.index('    let count = multiproof::node_count(Arity::Two, &idx[..d])')].count('\n')+1,'end_line':pins['batch_tree']['end_line']-1,'body_sha256':hashlib.sha256(tail.encode()).hexdigest(),'binding':'The exact terminal statements of batch_tree under an explicit argument environment; not a whole-call abstraction.'}
out=Path(__file__).resolve().parent/'BEf_native';(out/'src').mkdir(parents=True,exist_ok=True)
expected='\n\n'.join(parts)+'\n'
metadata={'source':str(source.relative_to(base)),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'functions':pins,'lowering':'Verbatim function items; only enclosing import environment supplied by the harness.'}
manifest=Path(__file__).resolve().parent/'BEf_native-source.json'
if '--check' in sys.argv:
    assert (out/'src'/'BEf_source.rs').read_text()==expected, 'verbatim source bodies changed'
    assert json.loads(manifest.read_text())==metadata, 'source manifest changed'
    print('PASS: complete source bodies, source fragments and manifest match exactly')
    raise SystemExit(0)
(out/'src'/'BEf_source.rs').write_text(expected)
manifest.write_text(json.dumps(metadata,indent=2)+'\n')
