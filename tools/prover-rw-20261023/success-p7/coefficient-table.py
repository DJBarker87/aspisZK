"""Generate/check the explicit P6 table, retaining native comparison separately."""
from pathlib import Path
import re,sys
r=Path(__file__).resolve().parents[3]
s=(r/'crates/aspis-core/src/r0/transport_pads.rs').read_text()
row=[int(x) for x in re.search(r'= \[([^]]*)\]',s)[1].split(',') if x.strip()]
assert len(row)==len(set(row))==89 and all(0<=x<1023 and x!=1014 for x in row)
order=row+[i for i in range(1023) if i not in set(row)]+[1023]
assert len(order)==1024 and set(order)==set(range(1024))
body='pub const COEFFICIENT_REFERENCE:[u16;1024]=[\n'+''.join(' '+','.join(map(str,order[i:i+32]))+',\n' for i in range(0,1024,32))+'];\n\npub fn coefficient_table()->[u16;1024] {COEFFICIENT_REFERENCE}\n'
p=Path(__file__).with_name('proof')/'table.rs'
if '--check' in sys.argv:assert p.read_text()==body
else:p.write_text(body)
