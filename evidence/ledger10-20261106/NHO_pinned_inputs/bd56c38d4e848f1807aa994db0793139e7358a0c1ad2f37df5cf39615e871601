from pathlib import Path
import subprocess,sys,json,hashlib
E=Path(__file__).resolve().parent;rows=[]
for n,target,expected in [(38,'KMX_ptr_correct',0),(39,'KMX_ptr_wrong',1),(40,'KMX_slice_wrong',1)]:
 a=f'NGU_K{n:03}';r=subprocess.run([sys.executable,str(E/'NGU_run.py'),a,'kani','verifier::NGU_stages::KMX_checks::'+target])
 raw=(E/a/'stdout.log').read_text()
 assert r.returncode==expected and ('VERIFICATION:- SUCCESSFUL' if expected==0 else 'VERIFICATION:- FAILED') in raw
 if expected:assert ' ** 1 of ' in raw
 rows.append(dict(attempt=a,harness=target,expected_exit=expected,exit=r.returncode,patch_sha256=hashlib.sha256((E/'NGU_KMX.patch').read_bytes()).hexdigest()))
(E/'NGU_FIDELITY.json').write_text(json.dumps(dict(exact_original_KMX_fixtures=rows,matching='K038/K039 pointer pair; K040 slice false-value control supplements every local positive/inverted-control family under identical original KMX generic stubs',same_deployed_features=True),indent=1)+'\n')
