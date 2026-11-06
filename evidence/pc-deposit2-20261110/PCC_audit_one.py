from pathlib import Path
import sys,subprocess,hashlib,json
b=Path.cwd();binary=b/'PCC_native/PCC_ProofDriver';mode=sys.argv[1]
before=hashlib.sha256(binary.read_bytes()).hexdigest()
r=subprocess.run([str(binary),mode])
after=hashlib.sha256(binary.read_bytes()).hexdigest();assert before==after
(b/('PCC_binary_'+mode+'.json')).write_text(json.dumps(dict(binary=str(binary),before=before,after=after,unchanged=True,exit=r.returncode)))
sys.exit(r.returncode)
