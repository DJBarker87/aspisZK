from pathlib import Path
import json,hashlib,subprocess
B=Path(__file__).resolve().parent;pins=json.loads((B/'NIX_SOURCE_PINS.json').read_text())
n='crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs';p=B/'NIX_src'/n;s=p.read_text();assert '#[cfg(kani)] mod NIX_more'not in s;p.write_text(s+(B/'NIX_more_copy.rs.txt').read_text())
n='crates/aspis-r1-cost-probe/src/r1_wire.rs';p=B/'NIX_src'/n;s=p.read_text();mark='#[cfg(kani)] pub mod NIX_round_constructor {';assert "pub fn record<'a>(row:u8,framed:"not in s;s=s.replace(mark,mark+"\n pub fn record<'a>(row:u8,framed:&'a[u8])->super::ValidatedRecord<'a>{super::ValidatedRecord{row,framed}}\n");p.write_text(s)
for n,h in pins.items():assert hashlib.sha256((B/'NIX_src'/n).read_bytes()).hexdigest()==h,('restoration pin mismatch',n)
p=B/'NIX_KANI_HELP.txt';r=subprocess.run(['/home/dombarker/.cargo/bin/cargo-kani','kani','--help'],stdout=p.open('w'),stderr=subprocess.STDOUT);assert r.returncode==0
print('All installed source pins restored exactly; no rebaseline. Future native jobs upload gate/pins only.')
