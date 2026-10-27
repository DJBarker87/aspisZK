from pathlib import Path
import subprocess,sys
p=Path(__file__).resolve().parent
sequence=[(12,'FJu_NativeInitial'),(13,'FJu_NativeChain'),(14,'FJu_EndpointIdentity'),(15,'FJu_LiteralForget'),(16,'FJu_ContForget'),(17,'FJu_CallerForget'),(18,'FJu_ResultForget'),(19,'FJu_Nonvacuity'),(20,'FJu_Conservativity'),(21,'FJu_ConservativityCheck'),(22,'FJu_Statements'),(23,'FJu_HypothesisAudit')]
for n,mod in sequence:
 print(f'Focused attempt {n}: {mod}',flush=True)
 r=subprocess.run([sys.executable,str(p/'FJu_compile.py'),str(n),mod])
 if r.returncode:sys.exit(r.returncode)
