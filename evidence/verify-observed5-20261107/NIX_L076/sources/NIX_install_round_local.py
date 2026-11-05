from pathlib import Path
import json,hashlib
B=Path(__file__).resolve().parent;n='crates/aspis-r1-cost-probe/src/r1_semantic.rs';p=B/'NIX_src'/n;s=p.read_text();s=s[:s.index('#[cfg(kani)] pub mod NIX_round')]+(B/'NIX_round_local.rs.txt').read_text();p.write_text(s)
nw='crates/aspis-r1-cost-probe/src/r1_wire.rs';p=B/'NIX_src'/nw;s=p.read_text();mark='#[cfg(kani)] pub mod NIX_round_constructor {';s=s.replace(mark,mark+"\n pub fn record<'a>(row:u8,framed:&'a[u8])->super::ValidatedRecord<'a>{super::ValidatedRecord{row,framed}}\n");p.write_text(s)
pins=json.loads((B/'NIX_SOURCE_PINS.json').read_text())
for x in [n,nw]:pins[x]=hashlib.sha256((B/'NIX_src'/x).read_bytes()).hexdigest()
(B/'NIX_SOURCE_PINS.json').write_text(json.dumps(pins));print('Prefix is an opaque borrowed-identity token; pure getter packet NIX_ProducerInstall.lookup supplies same row/frame. No physical-prefix assumption or new runtime trust.')
