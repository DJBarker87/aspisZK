from KMZ_lean import *
modules=json.loads((E/'KMZ_LEAN_MANIFEST.json').read_text())
assert len(modules)==57
for n,m in enumerate(modules,1):
 attempt=n if n<8 else n+1 if n<56 else n+2
 if compile_one(attempt,m)!=0:raise SystemExit('Focused source failed: '+m+'; correct/split before manifest')
assert compile_one(60,'KMZ_Final')==0
