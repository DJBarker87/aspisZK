from pathlib import Path
import re,subprocess,json,hashlib
E=Path(__file__).resolve().parent;rows=[]
for name,path in [('PoolV1PrivateTransferPublicV1','payment_relation.rs'),('PoolV1WithdrawalPublicV1','payment_relation.rs'),('PoolV1PairLatePublicStatementV1','pair_tree_profile.rs'),('PoolV1PairLiveSnapshotV1','pair_tree_profile.rs'),('PoolV1PairVerifiedAfterstateV1','pair_terminal.rs')]:
 p='crates/aspis-statement/src/pool_v1/'+path;raw=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p]);s=raw.decode();m=re.search(r'pub struct '+name+r'\s*\{[^}]*\}',s);assert m,name;rows.append(dict(type=name,frozen_path=p,source_sha256=hashlib.sha256(raw).hexdigest(),declaration=m.group(0)))
(E/'NMO_RAW_TYPE_INVENTORY.json').write_text(json.dumps(dict(review='Fields recursively contain only u8/u32/u64, M31(u32), and fixed arrays/structs of them; Digest is [M31;8]. No references, bool, enums or function pointers. Full initialized arbitrary bytes preserve the full typed input domain. Claims initializer checks size/alignment and writes every u32 before assume_init.',types=rows),indent=2)+'\n')
print('Recorded five frozen raw-constructor type declarations')
