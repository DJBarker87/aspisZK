from KNB_host import *
import sys
name=sys.argv[1]
admit('KNB_UPLOAD_'+name)
s=(E/('KNB_variant_'+name+'.rs.txt')).read_text()
r=py('from pathlib import Path\np=Path('+repr(B+'/KNB_src/crates/aspis-r1-cost-probe/src/NBZ_native.rs')+')\np.write_text('+repr(s)+')');assert r.returncode==0,r.stderr
