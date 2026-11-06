from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,m in [(121,'NLQ_WrongSplit'),(99,'NLQ_FirstWrongSplit'),(106,'NLQ_RuntimeCells'),(107,'NLQ_CopyMetadata'),(108,'NLQ_ProofPublicFrame'),(109,'NLQ_CheckpointRead'),(110,'NLQ_ZeroSite'),(111,'NLQ_SnapshotSecondDiv'),(112,'NLQ_SnapshotThirdDiv'),(113,'NLQ_ReplayThree'),(115,'NLM_SnapshotTrace'),(116,'NLM_SnapshotSkip'),(117,'NLQ_SnapshotSkip'),(118,'NLQ_InstalledStage1')]:
 r=subprocess.run([sys.executable,str(E/'NLQ_run.py'),f'NLQ_L{i:03d}','lean',m],capture_output=True,text=True)
 print(r.stdout.strip().splitlines()[-1] if r.stdout.strip() else m+': no output',flush=True)
 if r.returncode:raise SystemExit(r.returncode)
