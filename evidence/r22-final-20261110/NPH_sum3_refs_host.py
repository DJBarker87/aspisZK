#!/usr/bin/env python3
"""NPH_ (R22, SM sum3 context): read-only textual scan of the replayed L187 src tree. For the SM-copy
sum3 (AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared and _loop0) and the model
loops/bridges that call it, list every enclosing declaration and its kind. Run on the host from the
replay src directory: python3 NPH_sum3_refs_host.py > NPH_SUM3_REFS.json"""
import re,glob,json,sys
targets=["AspisR1PoseidonPreparedSum3Source.field.qm31_sum_products3_prepared","qm31_sum_products3_prepared_loop0",
 "FJe_Sum3IndexBridge.old","FJe_Sum3ChannelBridge.old","FJe_Sum3ComponentBridge.old",
 "PoseidonPreparedIndexActualLoop.Loop","PoseidonPreparedIndexActualLoopBuild.Loop","PoseidonPreparedIndexLoopExactV2.Loop",
 "PoseidonPreparedIndexLoopStep.Loop","PoseidonPreparedChannelLoopExact.Loop","PoseidonPreparedComponentLoopExact.Loop",
 "PoseidonPreparedComponentLoopExact.InnerLoop","PoseidonPreparedIndexLoopExactV2Fix4.Loop","PoseidonPreparedIndexLoopStep.ComponentLoop",
 "PoseidonPreparedIndexLoopExactV2Fix4.ComponentLoop"]
decl=re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |partial |unsafe )*(def|theorem|lemma|abbrev|instance|structure|example)\s+([^\s:({\[]+)",re.M)
out=[]
for f in sorted(glob.glob("**/*.lean",recursive=True)):
  t=open(f,errors="ignore").read()
  if not any(x in t for x in targets): continue
  ds=[(m.start(),m.group(1),m.group(2)) for m in decl.finditer(t)]
  seen=set()
  for x in targets:
    for m in re.finditer(re.escape(x),t):
      prev=[d for d in ds if d[0]<=m.start()]
      if not prev: continue
      k,n=prev[-1][1],prev[-1][2]
      if (k,n,x) in seen: continue
      seen.add((k,n,x)); out.append(dict(file=f,kind=k,decl=n,references=x))
json.dump(dict(note="enclosing declaration of each reference; FIq_Native* files hold the executing FIq copy whose names share the _loop0 suffix",refs=out),sys.stdout,indent=1)
