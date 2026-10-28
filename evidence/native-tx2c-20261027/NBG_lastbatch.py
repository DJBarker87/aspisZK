from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
stages=[
 ('NBG_K028','crates/aspis-core','field::NBG_runtime::NBG_square_iteration','NBG_square_step.patch'),
 ('NBG_K029','crates/aspis-core','field::NBG_runtime::NBG_scalar_embedding','NBG_scalar_embed.patch'),
 ('NBG_K030','crates/aspis-core','field::wide_exact::NBG_runtime::NBG_wide_writer_iteration','NBG_writer_step.patch'),
 ('NBG_K031','crates/aspis-core','field::wide_exact::NBG_runtime::NBG_raw_getters','NBG_raw_getters.patch'),
 ('NBG_K032','programs/r1-cost-probe','NBG_runtime::NBG_error_log','NBG_error.patch'),
]
if len(sys.argv)>1:
 stages=stages[:-1] if sys.argv[1]=='pre' else stages[-1:]
for a,c,h,p in stages:
 assert len(list(E.glob('NBG_K*/receipt.json')))<30,'STOP30 Kani budget'
 r=subprocess.run([sys.executable,str(E/'NBG_kani.py'),a,c,h,str(E/p)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout);print(a,'driver',r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
 print('result',json.loads((E/a/'receipt.json').read_text())['exit_status'],flush=True)
