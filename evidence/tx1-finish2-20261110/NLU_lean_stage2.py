from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for n,module in [(14,'NLU_Inspect'),(15,'NLU_TerminalDomain'),(16,'NLU_TerminalTransport'),(17,'NLU_Words')]:
 a=f'NLU_L{n:03}';subprocess.run([sys.executable,str(E/'NLU_config.py'),a,module],check=True)
 if subprocess.run([sys.executable,str(E/'NLU_run.py'),a]).returncode:sys.exit(1)
