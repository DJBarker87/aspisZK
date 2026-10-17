from pathlib import Path
import argparse,hashlib,re,json
ap=argparse.ArgumentParser();ap.add_argument('--repo',required=True,type=Path);a=ap.parse_args();base=Path(__file__).resolve().parent;p=a.repo/'docs/research/100bit-spend-path-20261013';raw=(base/'active-only-extraction/generated/AspisR1SelectedMaskProbe/Funs.lean').read_text();cut=(p/'lean/AspisR1SelectedMaskProbe/ActiveMaskBasisSourceSlice.lean').read_text()
start='/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::constants::ACTIVE_ROW_MASKS]';stop='/-- [aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::{aspis_r1_mask_extraction_probe::pool_v1::pair_forest_copy_terminal::Selectors}::active_mask_basis_probe]';r=raw[raw.index(start):raw.index(stop)].strip();c=cut[cut.index(start):cut.rindex('end AspisR1SelectedMaskProbe')];c=re.sub(r'^#print axioms .*\n','',c,flags=re.M).strip();assert r==c
m=json.loads((base/'active-slice-worker-map.json').read_text());assert hashlib.sha256(raw.encode()).hexdigest()==m['raw_aeneas_funs_sha256'];assert hashlib.sha256(cut.encode()).hexdigest()==m['source_slice_sha256']
assert hashlib.sha256((base/'candidate-copy-terminal.rs').read_bytes()).hexdigest()=='f38ca2bd28554e8f67b75b7b035f02648ea0b5d82f78d2457e10188e6402a3f0'
print('Active source cut matches generated declaration bytes, removing only print-axioms commands and surrounding whitespace')
