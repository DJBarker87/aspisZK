from pathlib import Path
import subprocess,sys
P=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(P/'NLR_run.py'),'NLR_L051'],check=True)
for n,h in [(38,'parse_error_cut'),(39,'parse_error_control'),(40,'independent_error_control')]:
 a=f'NLR_K{n:03d}'
 subprocess.run([sys.executable,str(P/'NLR_kconfig.py'),a,'r1_semantic::NLR_native::'+h],check=True)
 r=subprocess.run([sys.executable,str(P/'NLR_run.py'),a]);out=(P/a/'stdout.log').read_text()
 if n==38:assert r.returncode==0,(a,out[-1200:])
 else:assert 'VERIFICATION:- FAILED' in out and 'timed out' not in out and ('assertion' in out.lower() or (n==40 and 'core::panicking::assert_failed_inner' in out and '1 of 90 failed' in out)),(a,out[-1200:])
subprocess.run([sys.executable,str(P/'NLR_compile_batch.py')],check=True)
