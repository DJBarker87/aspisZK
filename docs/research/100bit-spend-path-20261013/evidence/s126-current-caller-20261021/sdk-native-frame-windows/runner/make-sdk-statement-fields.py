#!/usr/bin/env python3
"""Construct every field of the real frozen statement types symbolically.
No reduced carrier or canonicality assumption; all M31 storage words are u32.
Only padding bytes are omitted, since they are not Rust value fields.
"""
from pathlib import Path
import sys,re,json,subprocess,hashlib
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);O.mkdir(parents=True,exist_ok=True)
freeze='b2727acd3abf79315d18b754a260f58f4b1c6326'
files=['pair_forest_terminal','pair_tree_profile','payment_relation','pair_terminal']
sources={f:subprocess.check_output(['git','-C',str(R),'show',freeze+':crates/aspis-statement/src/pool_v1/'+f+'.rs'],text=True) for f in files}
names=['PoolV1PairForestTerminalCommonV1','PoolV1PairLatePublicStatementV1','PoolV1PairLiveSnapshotV1','PoolV1PairVerifiedAfterstateV1','PoolV1PrivateTransferPublicV1','PoolV1WithdrawalPublicV1']
rows={}
for name in names:
 hits=[(f,re.search(r'pub struct '+name+r'\s*\{([^}]+)\}',s)) for f,s in sources.items()]
 hits=[(f,m) for f,m in hits if m];assert len(hits)==1
 f,m=hits[0];body=re.sub(r'//[^\n]*','',m[1]);fields=re.findall(r'pub\s+(\w+)\s*:\s*([^,]+),',body)
 assert fields and not re.sub(r'pub\s+\w+\s*:\s*[^,]+,','',body).strip(),name
 rows[name]=dict(file=f,source=m[0],fields=[(n,t.strip()) for n,t in fields])
def value(typ):
 if typ in ['u8','u32','u64']:return 'kani::any::<'+typ+'>()'
 if typ=='M31':return 'aspis_core::field::M31(kani::any::<u32>())'
 if typ=='Digest':return 'core::array::from_fn(|_| '+value('M31')+')'
 if typ.startswith('['):
  base=typ[1:typ.index(';')].strip();return 'core::array::from_fn(|_| '+value(base)+')'
 assert typ in rows,typ
 return 'aspis_statement::pool_v1::'+typ+'{'+','.join(n+':'+value(t) for n,t in rows[typ]['fields'])+'}'
common=value('PoolV1PairForestTerminalCommonV1')
text='fn statement()->PoolV1PairForestTerminalStatementV1 {\n let common='+common+';\n if kani::any::<bool>() {\n PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,public:'+value('PoolV1PrivateTransferPublicV1')+'}\n } else {\n PoolV1PairForestTerminalStatementV1::Withdrawal{common,public:'+value('PoolV1WithdrawalPublicV1')+'}\n }\n}\n'
(O/'statement.rs').write_text(text)
(O/'statement-fields.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',freeze=freeze,qualification=__doc__,source_sha256=hashlib.sha256(text.encode()).hexdigest(),types=rows),indent=2)+'\n')
