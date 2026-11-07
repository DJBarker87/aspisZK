#!/usr/bin/env python3
"""Read immutable git inputs without expanding the sparse checkout."""
import subprocess,json,re,hashlib,collections
from pathlib import Path
E=Path(__file__).resolve().parent
REV=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
def read(p):return subprocess.check_output(['git','show',REV+':'+p])
def main():
 x=json.loads(read('evidence/emission-audit-20261109/NKT_EXTRACTIONS.json'))
 out=[]
 for z in x:
  if z['origin_status']=='HASH_LINKED_PIN_RECEIPT':continue
  p=z['emission_paths'][0];b=read(p);assert hashlib.sha256(b).hexdigest()==z['extraction_id'];s=b.decode()
  annotations=re.findall(r'/--\s*\[([^\]\n]+)\][\s\S]*?Source: \'([^\']+)\'',s)
  out.append(dict(blob=z['extraction_id'],paths=z['emission_paths'],origin_status=z['origin_status'],bytes=len(b),crate_header=re.findall(r'^-- \[([^]]+)\]:',s,re.M),namespace=re.findall(r'^namespace (\S+)',s,re.M),annotations=[dict(name=n,source=p) for n,p in annotations],definitions=re.findall(r'^(?:noncomputable )?(?:def|abbrev|inductive|structure)\s+([^\s:{(]+)',s,re.M),pin_receipt_paths=sorted({p['path'] for p in z['pin_receipts']})))
 (E/'NMH_INVENTORY.json').write_text(json.dumps(dict(revision=REV,blobs=out),indent=2)+'\n')
 print(json.dumps(dict(blobs=len(out),bytes=sum(z['bytes'] for z in out),native_headers=collections.Counter(c for z in out for c in z['crate_header']))))
if __name__=='__main__':main()
