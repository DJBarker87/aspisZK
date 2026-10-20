#!/usr/bin/env python3
from pathlib import Path
import subprocess,sys,json,hashlib
here=Path(__file__).resolve().parent;area=here.parents[1]
subprocess.run([sys.executable,str(here/'extract-canonical-reader.py'),'--check'],check=True)
subprocess.run([sys.executable,str(here/'emit-canonical-readers.py'),'--check'],check=True)
for ns,sub in [('AspisR1CanonicalReader','canonical-reader'),('AspisR1CanonicalKReader','canonical-kreader')]:
 for name in ['Funs.lean']:
  raw=(here/(sub+'-generated')/name).read_text()
  if name=='Funs.lean':raw=raw.replace('namespace '+ns+'\n','namespace '+ns+'\nvariable [Runtime]\n')
  assert raw==(area/'lean'/ns/name).read_text(),(ns,name)
assert (here/'canonical-reader-input/field.rs').read_bytes()==(here/'canonical-inputs-input/field.rs').read_bytes()
assert (here/'canonical-reader-input/field/wide_exact.rs').read_bytes()==(here/'canonical-inputs-input/field/wide_exact.rs').read_bytes()
print(json.dumps(dict(raw_types_normalization='Only fully-qualified generated discriminator registration; constructors/order/ordinals unchanged',funs_only_normalization='Explicit Runtime parameter for unchanged Reader.raw; no raw-byte property assumed',strict_parser='Existing extracted strict parser; coordinate copies',complete_source_field_files_identical=True,stdlib_ok_or='Existing exact stdlib body AspisR1CanonicalStd.ok_or')))
