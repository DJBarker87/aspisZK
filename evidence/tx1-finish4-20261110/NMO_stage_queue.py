from pathlib import Path
import subprocess,sys,json,lzma
E=Path(__file__).resolve().parent
for n,h,bad in [(7,'NMO_claims_reply_control',True),(8,'NMO_claims_argument_control',True),(9,'NMO_claims_footprint_control',True),(10,'NMO_claims_error_stability',False)]:
 a=f'NMO_K{n:03}';subprocess.run([sys.executable,str(E/'NMO_kconfig.py'),a,'r1_semantic::NMO_stage::'+h],check=True)
 subprocess.run([sys.executable,str(E/'NMO_run.py'),a])
 p=E/a/'receipt.json';assert p.exists(),'Recover read-only; no further scope'
 r=json.loads(p.read_text());s=p.parent/'stdout.log';log=s.read_text()if s.exists()else lzma.decompress(s.with_suffix('.log.xz').read_bytes()).decode()
 assert r['exit_status']==int(bad) and ('VERIFICATION:- FAILED'if bad else'VERIFICATION:- SUCCESSFUL')in log and 'timed out'not in log,'Review unexpected verdict'
subprocess.run([sys.executable,str(E/'NMO_config.py'),'NMO_L005','NMO_PrefixErrors'],check=True)
subprocess.run([sys.executable,str(E/'NMO_run.py'),'NMO_L005'],check=True)
