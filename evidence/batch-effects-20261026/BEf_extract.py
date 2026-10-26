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
out=Path(__file__).resolve().parent/'BEf_native';(out/'src').mkdir(parents=True,exist_ok=True)
expected='\n\n'.join(parts)+'\n'
if '--check' in sys.argv:
    assert (out/'src'/'BEf_source.rs').read_text()==expected, 'verbatim source bodies changed'
    print('PASS: ten complete native source bodies match exactly')
    raise SystemExit(0)
(out/'src'/'BEf_source.rs').write_text(expected)
(Path(__file__).resolve().parent/'BEf_native-source.json').write_text(json.dumps({'source':str(source.relative_to(base)),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'functions':pins,'lowering':'Verbatim function items; only enclosing import environment supplied by the harness.'},indent=2)+'\n')
