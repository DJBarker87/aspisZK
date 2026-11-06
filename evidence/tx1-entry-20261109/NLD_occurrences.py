"""Pin the five frozen entry bodies and preserve ledger obligations verbatim."""
from pathlib import Path
import hashlib,json,lzma,subprocess
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
p=E/'NLD_BASELINE_ROWS.json'
raw=p.read_bytes()if p.exists()else lzma.decompress((E/'NLD_BASELINE_ROWS.json.xz').read_bytes())
rows=json.loads(raw)
compact=[]
for r in rows:
 c=r['obligation']['certificate'];compact.append(dict(row=r['row'],function=r['function'],frozen_revision=REV,frozen_body_sha256=r['obligation']['frozen_body_sha256'],kernel_roots=r['obligation']['kernel_roots'],named_hypotheses=r['obligation']['named_hypotheses'],inventory_domain_obligations=r['obligation']['inventory_domain_obligations'],caller_domain_obligations=r['obligation']['caller_domain_obligations'],certificate_callees=c.get('canonical_callees'),typed_packet_statement_present=False))
(E/'NLD_OBLIGATIONS.json').write_text(json.dumps(compact,indent=1)+'\n')
pins=[]
for rel in ['programs/r1-cost-probe/src/lib.rs','programs/r1-cost-probe/src/r1_pool_adapter.rs','programs/r1-cost-probe/src/r1_pool_adapter_owned.rs','Cargo.lock']:
 b=subprocess.check_output(['git','show',REV+':'+rel]);actual=Path(rel).read_bytes();assert b==actual,rel
 pins.append(dict(path=rel,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),revision=REV,worktree_identical=True))
(E/'NLD_FROZEN_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
# Retain the large recursive baseline input once, content-addressed by SHA256.
p=E/'NLD_BASELINE_ROWS.json';(E/'NLD_BASELINE_ROWS.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'NLD_BASELINE_ROWS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n');p.unlink(missing_ok=True)
