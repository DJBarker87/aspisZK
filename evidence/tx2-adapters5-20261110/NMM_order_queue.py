from NMM_order_native import *
import sys
start=int(sys.argv[1])
for i,mode in enumerate(sys.argv[2:] or ['positive','spec','argument','footprint','copy']):
 a='NMM_K'+str(start+i).zfill(3);r=attempt(a,mode);out=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 expected=0 if mode=='positive' else 1
 assert r['exit_status']==expected and ('VERIFICATION:- SUCCESSFUL' in out if not expected else 'VERIFICATION:- FAILED' in out) and 'timed out' not in out.lower(),'Inspect '+a
