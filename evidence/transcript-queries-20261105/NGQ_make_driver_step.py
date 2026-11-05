"""Install the reviewed actual-QueryScan boundary transcription, preserving later cuts.
Supersedes the Fields-only prototype; this is not a whole sampler certificate.
"""
from pathlib import Path
import sys
E=Path(__file__).resolve().parent;p=E/'NGQ_core_harness.rs.txt';old=p.read_text()
prefix,rest=old.split('// NGQ generated outer cut\n',1)
_,suffix=rest.split('// Split K044:',1)
new=prefix+'// NGQ generated outer cut\n'+(E/'NGQ_outer_native.rs.txt').read_text()+'// Split K044:'+suffix
if '--check' in sys.argv:assert new==old
else:p.write_text(new)
