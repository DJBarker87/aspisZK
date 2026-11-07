from NMD_formal import *
import subprocess
subprocess.run([sys.executable,str(E/'NMD_program_queue.py'),'64'],check=True)
subprocess.run([sys.executable,str(E/'NMD_actual.py'),'NMD_K070','verifier::candidate::NMD_native::NMD_actual_parse_contract'],check=True)
