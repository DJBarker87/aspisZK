from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
names=['pool_v1::payment_relation::NBP_codecs::NBP_store_'+v for v in ['magic','pool','deployment','sequence','anchor','nullifier','asset','recipient','change','amount','destination']]
raise SystemExit(subprocess.run([sys.executable,str(E/'NBP_kaniserial.py'),'19','crates/aspis-statement',str(E/'NBP_statement.patch'),*names]).returncode)
