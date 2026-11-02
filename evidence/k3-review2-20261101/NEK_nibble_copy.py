"""Official KMX positive/failing controls in each exact nibble source configuration."""
from NEK_priority import *
rp='evidence/native-front4b-20261028/NDM_K009/receipt.json'
for j,src in enumerate(range(235,239)):
 o=read_json(E/f'NEK_K{src:03}_overlay.json')
 for neg in [False,True]:
  a=f'NEK_K{327+2*j+int(neg):03}'
  if (E/a/'receipt.json').exists():continue
  os.environ['NEK_HARNESS']='NEK_kmx::KMX_checks::'+('KMX_ptr_wrong' if neg else 'KMX_ptr_positive')
  try:v=publish(a,rp,o,neg,'official KMX configuration control for exact nibble window NEK_K'+str(src))
  finally:os.environ.pop('NEK_HARNESS',None)
  if v=='OPEN':raise SystemExit('incomplete configuration control')
