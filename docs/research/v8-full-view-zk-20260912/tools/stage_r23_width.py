#!/usr/bin/env python3
"""Stage one guarded integer-width rewrite on the frozen R22 comparison."""
import argparse,hashlib,json,shutil,subprocess,sys
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--control',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();here=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(here/'stage_r22_native.py'),'--control',str(a.control),'--output',str(a.output)],check=True)
dst=a.output;ex=dst/'docs/research/v8-no-work-100-20260907/experiments';path=dst/'crates/aspis-core/src/field.rs';original=path.read_text()
shutil.copy2(path,ex/'r23_reference_field.rs')
mul='(u64::from(self.a.0) + u64::from(self.b.0)) * (u64::from(rhs.a.0) + u64::from(rhs.b.0))'
square='(u64::from(self.a.0) + u64::from(self.b.0))\n                    * (u64::from(self.a.0) + u64::from(P) - u64::from(self.b.0))'
assert original.count(mul)==1 and original.count(square)==1
text=original.replace(mul,'r23_product_u32_bounded(u64::from(self.a.0) + u64::from(self.b.0), u64::from(rhs.a.0) + u64::from(rhs.b.0))').replace(square,'r23_product_u32_bounded(u64::from(self.a.0) + u64::from(self.b.0), u64::from(self.a.0) + u64::from(P) - u64::from(self.b.0))')
text+='\ninclude!("r23_width.rs");\n';path.write_text(text)
shutil.copy2(here/'r23_width.rs',path.parent/'r23_width.rs')
shutil.copy2(here/'r23_field_check.rs',ex/'r23_field_check.rs')
host=ex/'r22_check.rs';text=host.read_text();assert text.count('fn main(){')==1
host.write_text('include!("r23_field_check.rs");\n'+text.replace('fn main(){','fn main(){\n    r23_field_check();'))
manifest=dst/'r18-stage.json';m=json.loads(manifest.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
changed=[path,path.parent/'r23_width.rs',host,ex/'r23_field_check.rs',ex/'r23_reference_field.rs']
for p in changed:m['files'][str(p.relative_to(dst))]=sha(p)
m['r23_width']={'rewrite_sites':2,'original_field_sha256':sha(ex/'r23_reference_field.rs'),'reference_revision':'fbd5e9ac362b16713f828c1a1508af497d5d9e6d','overflow_checks_retained':True,'fallback_original_checked_product':True}
manifest.write_text(json.dumps(m,indent=2)+'\n');print(json.dumps({'pins':len(m['files']),'stage':str(dst)}))
