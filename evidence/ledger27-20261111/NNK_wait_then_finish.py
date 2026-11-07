from pathlib import Path
import time,subprocess,sys
E=Path(__file__).resolve().parent
while not(E/'NNK_L053/receipt.json').exists()or(E/'NNK_CLIENT_ACTIVE').exists():time.sleep(2)
# The serial audit queue has no submissions after053. Its last client is fully finished.
raise SystemExit(subprocess.run([sys.executable,str(E/'NNK_finish_queue.py')]).returncode)
