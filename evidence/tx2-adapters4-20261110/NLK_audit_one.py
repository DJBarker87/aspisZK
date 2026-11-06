from pathlib import Path
import sys,subprocess,hashlib,json
b=Path.cwd();binary=b/sys.argv[1];mode=sys.argv[2];expected=sys.argv[3]
before=hashlib.sha256(binary.read_bytes()).hexdigest();assert before==expected
r=subprocess.run([str(binary),mode]);after=hashlib.sha256(binary.read_bytes()).hexdigest();assert before==after
(b/('NLK_binary_'+mode+'.json')).write_text(json.dumps(dict(binary=str(binary),before=before,after=after,unchanged=True,exit=r.returncode)))
sys.exit(r.returncode)
