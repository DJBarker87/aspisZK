"""Sequential compile of one module, then optimized link, within one fixed scope."""
import subprocess,sys
r=subprocess.run(sys.argv[1:])
if r.returncode:sys.exit(r.returncode)
T='/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0'
r=subprocess.run([T+'/bin/lake','env','leanc','-O3','-rdynamic','-o','NNO_native/NNO_Scan','NNO_native/NNO_Scan.c','NNO_native/NFA_WALKER.c','NNO_native/NFA_MemoryLimit.c'])
sys.exit(r.returncode)
