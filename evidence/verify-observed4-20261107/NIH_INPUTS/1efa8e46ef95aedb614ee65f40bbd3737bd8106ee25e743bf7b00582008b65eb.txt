from pathlib import Path
import json,hashlib
B=Path(__file__).resolve().parent;S=B/'NIH_src';pins=json.loads((B/'NIH_SOURCE_PINS.json').read_text())
for q,n in [('crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs','NIH_copy_terminal.rs.txt'),('crates/aspis-statement/src/pool_v1/NIH_copy.rs','NIH_copy.rs.txt'),('crates/aspis-statement/src/NIH_raw_extension.rs','NIH_raw_extension.rs.txt')]:
 p=S/q;p.write_text((B/n).read_text());pins[q]=hashlib.sha256(p.read_bytes()).hexdigest()
q='crates/aspis-statement/src/state_only_poseidon.rs';p=S/q;old=p.read_text();needle='fn extension_from_raw_limbs(limbs: [u64; 4]) -> QM31 {';assert old.count(needle)==1
attrs=json.loads((B/'NIH_CONSTRUCTOR_CONTRACTS.json').read_text())['raw_attribute'];assert attrs not in old;new=old.replace(needle,attrs+needle);assert new.replace(attrs,'')==old;p.write_text(new);pins[q]=hashlib.sha256(p.read_bytes()).hexdigest()
(B/'NIH_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
