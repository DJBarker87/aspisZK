from pathlib import Path
import subprocess,os,sys
E=Path(__file__).resolve().parent
cases=[('025','NEF_copy_positive','NEF_bad_nonempty'),('026','NEF_copy_negative','NEF_bad_nonempty'),
('027','NEF_inv_log','NEF_bad_inv_input'),('028','NEF_inv_log','NEF_bad_inv_reply'),('029','NEF_inv_log','NEF_bad_inv_order'),('030','NEF_inv_log','NEF_bad_inv_tag'),
('031','NEF_query_nonempty_tail','NEF_bad_rhs'),('032','NEF_query_nonempty_tail','NEF_bad_len'),
('033','NEF_inv_log','NEF_bad_aa'),('034','NEF_inv_log','NEF_bad_bb'),('035','NEF_inv_log','NEF_bad_norm_add'),('036','NEF_inv_log','NEF_bad_neg'),('037','NEF_inv_log','NEF_bad_out_a'),('038','NEF_inv_log','NEF_bad_out_b'),
('039','NEF_query_tail_frame','NEF_bad_terms'),('040','NEF_mark_frame','NEF_bad_error_result')]
for a,fn,cfg in cases:
 r=subprocess.run([sys.executable,str(E/'NEF_run.py'),'NEF_K'+a,'kani','verifier::candidate::NEF_native::'+fn],env=dict(os.environ,NEF_CFG=cfg));assert r.returncode==0
