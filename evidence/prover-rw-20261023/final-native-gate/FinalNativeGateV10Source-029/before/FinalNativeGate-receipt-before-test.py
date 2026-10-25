"""Actual pre-repair filesystem counterexample, not remote umask evidence."""
import os, stat, tempfile
from pathlib import Path
import FinalNativeGate_setup as setup
root=Path(tempfile.mkdtemp(prefix='FinalNativeGate-receipt-before-',dir='/private/tmp'))
assert stat.S_IMODE(root.stat().st_mode)==0o700
setup.PACKET=root
old=os.umask(0o002)
try:
    receipt=setup._publish('FinalNativeGate-setup-parent-terminal.json',{'fixture':'local only'})
    mode=stat.S_IMODE((root/receipt['name']).stat().st_mode)
    assert mode==0o664,oct(mode)
    assert mode&0o022
    print(dict(retained=str(root),mode=oct(mode),original_receiver_predicate=False,real_host_umask='UNOBSERVED'))
finally:os.umask(old)
