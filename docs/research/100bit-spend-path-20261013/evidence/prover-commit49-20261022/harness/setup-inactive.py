from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent.parent;D=E/'inactive-owner';D.mkdir(exist_ok=True)
p=Path('crates/aspis-core/src/r0/opening.rs');s=p.read_text();m=re.search(r'pub const COPY_ACTIVE_ROW_MASKS: \[u16; 64\] = (\[.*?\]);',s,re.S);table=m[1]
(D/'Cargo.toml').write_text('[package]\nname="simulator-inactive-owner49"\nversion="0.1.0"\nedition="2021"\n[lib]\npath="lib.rs"\n[workspace]\n')
(D/'lib.rs').write_text('''pub mod owned {
pub const MASKS:[u16;64]='''+table+''';
pub fn row(j:usize)->usize {
 (j/64)%4+4*((j/256)%4)+16*((j/16)%4)+64*(j%4)+256*((j/4)%4)
}
pub fn inactive(j:usize)->bool {
 let r=row(j);(MASKS[r/16] >> ((r%16) as u32))&1==0
}
}
''')
s=(E/'harness/extract-weights.py').read_text().replace('weight-owner','inactive-owner').replace('WeightOwner','InactiveOwner');(E/'harness/extract-inactive.py').write_text(s)
(E/'pins/inactive-table-source.json').write_text(json.dumps(dict(source=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),literal_table=table),indent=2)+'\n')
