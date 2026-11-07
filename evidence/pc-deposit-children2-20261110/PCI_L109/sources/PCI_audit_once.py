"""Pin the same binary and C walker before and after every audit mode."""
from pathlib import Path
import hashlib,json,subprocess,sys
B=Path.cwd();mode=sys.argv[1]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
names=['PCI_native/PCI_AuditDriver','PCI_native/PCI_AuditDriver.c','PCI_native/PCI_WALKER.c','PCI_native/PCI_MemoryLimit.c']
pins={n:sha(B/n) for n in names};base=B/'PCI_BINARY_BASE.json'
if base.exists():assert json.loads(base.read_text())==pins
else:
 assert mode=='fixtures';base.write_text(json.dumps(pins))
r=subprocess.run([str(B/'PCI_native/PCI_AuditDriver'),mode])
assert all(sha(B/n)==v for n,v in pins.items())
(B/('PCI_BINARY_'+mode+'.json')).write_text(json.dumps(dict(before=pins,after=pins,unchanged=True)))
sys.exit(r.returncode)
