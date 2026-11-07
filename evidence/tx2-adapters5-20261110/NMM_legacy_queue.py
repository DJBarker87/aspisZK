from NMM_legacy_native import *
import sys
start=int(sys.argv[1]);branch=sys.argv[2];version=sys.argv[3]
for i,mode in enumerate(sys.argv[4:] or ['positive','reply','argument','footprint','copy']):
 a='NMM_K'+str(start+i).zfill(3);r=attempt(a,mode,branch,version)
 out=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 expected=0 if mode=='positive' else 1
 assert r['exit_status']==expected and ('VERIFICATION:- SUCCESSFUL' in out if not expected else 'VERIFICATION:- FAILED' in out) and 'timed out' not in out.lower(),'Unexpected verdict; inspect '+a
