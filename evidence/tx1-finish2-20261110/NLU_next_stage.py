from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for n,module in [(56,'NLU_TerminalTransport'),(57,'NLU_Words'),(58,'NLU_HighCut'),(59,'NLU_InputDomain')]:
 a=f'NLU_L{n:03}';subprocess.run([sys.executable,str(E/'NLU_config.py'),a,module],check=True)
 if subprocess.run([sys.executable,str(E/'NLU_run.py'),a]).returncode:sys.exit(1)
