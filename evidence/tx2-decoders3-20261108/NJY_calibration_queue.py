from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
assert (E/'NJY_K074/receipt.json').exists()
for n,f in [(75,'words'),(79,'step_post'),(83,'bindings'),(87,'digest')]:
 for d,m in enumerate(['positive','inverse','unimplied','modifies']):
  subprocess.run([sys.executable,str(E/'NJY_intermediate_shapes.py'),f'NJY_K{n+d:03}',f,m],check=True)
