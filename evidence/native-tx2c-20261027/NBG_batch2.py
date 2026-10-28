"""Serial continuation; no dependence on unrelated open members."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
stages=[
 ('NBG_K014','crates/aspis-core','field::wide_exact::NBG_runtime::NBG_limbs','NBG_wide.patch'),
 ('NBG_K015','crates/aspis-core','field::wide_exact::NBG_runtime::NBG_wide_constructors','NBG_wide.patch'),
 ('NBG_K016','crates/aspis-core','field::wide_exact::NBG_runtime::NBG_wide_add_sub','NBG_wide.patch'),
 ('NBG_K017','crates/aspis-core','field::wide_exact::NBG_runtime::NBG_wide_decode','NBG_wide.patch'),
 ('NBG_K018','crates/aspis-statement','atomic_statement::NBG_runtime::NBG_unwrap_ok','NBG_statement.patch'),
 ('NBG_K019','crates/aspis-statement','atomic_statement::NBG_runtime::NBG_digest_decode','NBG_statement.patch'),
 ('NBG_K020','crates/aspis-statement','atomic_statement::NBG_runtime::NBG_encode_digest_step','NBG_statement.patch'),
 ('NBG_K021','crates/aspis-statement','pool_v1::payment_relation::NBG_runtime::NBG_digest_canonical','NBG_statement.patch'),
 ('NBG_K022','crates/aspis-statement','pool_v1::payment_relation::NBG_runtime::NBG_projections','NBG_statement.patch'),
 ('NBG_K023','crates/aspis-statement','pool_v1::payment_relation::NBG_runtime::NBG_common_validation','NBG_statement.patch'),
 ('NBG_K024','crates/aspis-statement','pool_v1::payment_relation::NBG_runtime::NBG_transfer_validation','NBG_statement.patch'),
 ('NBG_K025','crates/aspis-statement','pool_v1::payment_relation::NBG_runtime::NBG_withdrawal_validation','NBG_statement.patch'),
 ('NBG_K026','crates/aspis-statement','pool_v1::payment_relation::NBG_runtime::NBG_header','NBG_statement.patch'),
 ('NBG_K027','crates/aspis-core','field::NBG_runtime::NBG_reduce_all_u64','NBG_reduction.patch'),
]
for a,c,h,p in stages:
 r=subprocess.run([sys.executable,str(E/'NBG_kani.py'),a,c,h,str(E/p)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout);print(a,'driver',r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
 rc=json.loads((E/a/'receipt.json').read_text());print('result',rc['exit_status'],flush=True)
