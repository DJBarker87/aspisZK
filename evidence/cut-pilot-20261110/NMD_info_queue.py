from NMD_formal import *
import subprocess,os
subprocess.run([sys.executable,str(E/'NMD_newest_run.py'),'NMD_K087','verifier::candidate::NEF_native::NEF_none_control'])
subprocess.run([sys.executable,str(E/'NMD_newest_run.py'),'NMD_K088','verifier::candidate::NBZ_native::NBZ_return_carriers'],env=dict(os.environ,NMD_INFO_PINNED='1'))
subprocess.run([sys.executable,str(E/'NMD_guard_queue.py'),'89'],check=True)
subprocess.run([sys.executable,str(E/'NMD_gate_queue.py')],check=True)
