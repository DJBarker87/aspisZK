"""Read-only three-ELF identity and retained-key mode receipt."""
from pathlib import Path
import json,hashlib,stat
h=Path('/home/dombarker/project-offloads/codex-cx-prover-dict-20261026');rows=[]
for mode,pin,name,job in [
 ('default','d7d42f770883401e0104fb6e044f61a132fea7359943db225d581c5740fcffd0','aspis_r1_cost_probe_program.so','pdict-elf-default-004'),
 ('devnet','2b2a9f0e7a2f93004ddbf207d02f5c5d5155d5c9bfdaeed21a78d638ae9be922','aspis_r1_cost_probe_program.so','pdict-elf-devnet-001'),
 ('pool','121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548','aspis_pool.so','pdict-elf-pool-003')]:
 p=h/'artifacts'/('pdict-'+mode)/name;sha=hashlib.file_digest(p.open('rb'),'sha256').hexdigest();rec=json.loads((h/'src/receipts'/job/'receipt.json').read_text());keys=[]
 for k in p.parent.glob('*keypair.json'):
  m=stat.S_IMODE(k.stat().st_mode);assert m==0o600;keys.append(dict(path=str(k),mode=oct(m),retained=True))
 rows.append(dict(mode=mode,artifact=str(p),bytes=p.stat().st_size,sha256=sha,expected_sha256=pin,byte_equal=sha==pin,receipt=job,build_exit=rec['exit_status'],wall_seconds=rec['wall_seconds'],peak_rss_kib=rec['peak_rss_kib'],swaps=rec['swaps'],retained_keys=keys))
out=dict(rows=rows,passed=all(z['byte_equal'] for z in rows),scope='Fresh owned snapshot normal SBF builds; not release/adoption evidence. Subsequent Rust edits are append-only cfg(kani), with unchanged production prefixes independently checked. No further current-raw-source rebuild claimed.',unchanged_pins=True)
(h/'receipts/elf-identities.json').write_text(json.dumps(out,indent=2)+'\n');print([(z['mode'],z['byte_equal']) for z in rows])
