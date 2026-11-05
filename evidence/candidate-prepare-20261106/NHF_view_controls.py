"""Add two matched corruptions to the SAME local-record decoder boundary."""
from pathlib import Path
import json,hashlib,difflib
E=Path(__file__).resolve().parent;p=E/'NHF_wide.rs.txt';s=p.read_text()
s=s.replace('proof[compact::OFF_INACTIVE..compact::OFF_ROUND0]','proof[compact::OFF_INACTIVE+usize::from(cfg!(NHF_bad_decode_arg))..compact::OFF_ROUND0]')
a=s.index(' self.reply}',s.index('impl DecodeLog'))
s=s[:a]+''' if cfg!(NHF_bad_reply){if let Some(value)=self.reply{let mut limbs=value.to_limbs();limbs[0]=if limbs[0]==0{1}else{0};return E::from_limbs(limbs);}}
'''+s[a:]
p.write_text(s)
pins=json.loads((E/'NHF_SOURCE_PINS.json').read_text());pins['crates/aspis-r1-cost-probe/src/NHF_wide.rs']=hashlib.sha256(s.encode()).hexdigest();(E/'NHF_SOURCE_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
p=E/'NHF_native.patch';patch=p.read_text();a=patch.index('--- /dev/null\n+++ b/crates/aspis-r1-cost-probe/src/NHF_wide.rs\n');p.write_text(patch[:a]+''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/crates/aspis-r1-cost-probe/src/NHF_wide.rs')))
p=E/'NHF_run.py';s=p.read_text().replace(" if os.environ.get('NHF_BAD_STAGE'):"," if os.environ.get('NHF_BAD_DECODE_ARG'):config['env']['RUSTFLAGS']+=' --cfg NHF_bad_decode_arg'\n if os.environ.get('NHF_BAD_REPLY'):config['env']['RUSTFLAGS']+=' --cfg NHF_bad_reply'\n if os.environ.get('NHF_BAD_STAGE'):");p.write_text(s)
