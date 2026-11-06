from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for n,module in [(10,'NLU_FoldProjection'),(11,'NLU_SourceProjection'),(12,'NLU_Linear'),(13,'NLU_TerminalDomain'),(14,'NLU_Inspect'),(15,'NLU_TerminalTransport')]:
 a=f'NLU_L{n:03}'
 subprocess.run([sys.executable,str(E/'NLU_config.py'),a,module],check=True)
 if subprocess.run([sys.executable,str(E/'NLU_run.py'),a]).returncode:sys.exit(1)
