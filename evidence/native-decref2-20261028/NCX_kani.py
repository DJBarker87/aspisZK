from pathlib import Path
import sys
from NCX_run import launch
from NCX_instrument import files
E=Path(__file__).resolve().parent
a,target=sys.argv[1:]
f={'NCX_src/'+p:s for p,s in files().items()}
f['NCX_gate.py']=(E/'NCX_gate.py').read_text()
f['NCX_frozen_graph.sha256']=Path('evidence/native-decref-20261028/NCV_frozen_graph.sha256').read_text()
launch(a,'kani',target,f,['python3','NCX_gate.py',a,target],list(f)+['NCX_src/Cargo.lock','NCX_KMX_copy_stubs.patch'],600)
