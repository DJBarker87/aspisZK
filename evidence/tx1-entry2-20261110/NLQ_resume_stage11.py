from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for i,m in [(104,'NLQ_DispatchSource'),(105,'NLQ_ReplayNormal'),(84,'NLQ_Stage1Fold'),(85,'NLQ_Stage1Parent'),(86,'NLQ_Stage1Guard'),(87,'NLQ_Stage1Body'),(88,'NLQ_WritebackFrame'),(89,'NLQ_PublicRead'),(90,'NLQ_ProofRead'),(91,'NLQ_OwnedGuard'),(67,'NLM_DeployedOps'),(94,'NLQ_InspectPorts'),(95,'NLQ_EntryRejection'),(96,'NLQ_ReplayAbort'),(97,'NLQ_Stage1Abort'),(98,'NLQ_WrongSplit'),(99,'NLQ_FirstWrongSplit'),(106,'NLQ_RuntimeCells'),(107,'NLQ_CopyMetadata'),(108,'NLQ_ProofPublicFrame'),(109,'NLQ_CheckpointRead'),(110,'NLQ_ZeroSite'),(111,'NLQ_SnapshotSecondDiv'),(112,'NLQ_SnapshotThirdDiv'),(113,'NLQ_ReplayThree')]:
 r=subprocess.run([sys.executable,str(E/'NLQ_run.py'),f'NLQ_L{i:03d}','lean',m],capture_output=True,text=True)
 print(r.stdout.strip().splitlines()[-1] if r.stdout.strip() else m+': no output',flush=True)
 if r.returncode:raise SystemExit(r.returncode)
