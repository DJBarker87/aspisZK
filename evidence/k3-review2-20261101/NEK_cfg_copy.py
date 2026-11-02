"""Exact KMX controls for native-step cfgs consumed by the NEB closure."""
from NEK_priority import *
for j,src in enumerate([1,3,7]):
 o=read_json(E/f'NEK_K{src:03}_overlay.json');old=read_json(E/f'NEK_K{src:03}/receipt.json');rp=old['deps_fingerprint']['original_receipt']
 for neg in [False,True]:
  a=f'NEK_K{336+2*j+int(neg):03}'
  if (E/a/'receipt.json').exists():continue
  os.environ['NEK_HARNESS']='NEK_kmx::KMX_checks::'+('KMX_ptr_wrong' if neg else 'KMX_ptr_correct')
  try:v=publish(a,rp,o,neg,'exact KMX configuration control with the unchanged native-step overlay/flags of NEK_K'+str(src))
  finally:os.environ.pop('NEK_HARNESS',None)
  if v=='OPEN':raise SystemExit('incomplete cfg control')
