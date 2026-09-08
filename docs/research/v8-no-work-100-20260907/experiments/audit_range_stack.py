#!/usr/bin/env python3
"""Audit final emitted static frame accesses; not a whole machine-code proof."""
import re,sys,json
text=sys.stdin.read()
name="<unknown>"; maxima={}; seen=set()
for line in text.splitlines():
    m=re.match(r"^[0-9a-f]+ <(.+)>:",line)
    if m: name=m[1];seen.add(name)
    for raw in re.findall(r"r10 - 0x([0-9a-f]+)",line):
        maxima[name]=max(maxima.get(name,0),int(raw,16))
assert maxima,"no final frame accesses"
old=[n for n in seen if "verify_reconstruct_and_gamma_combine_v7_openings" in n]
print(json.dumps({"max_direct_frame_offset":max(maxima.values()),
  "functions_with_direct_frame_accesses":len(maxima),"unused_warning_function_emitted":old,
  "largest":sorted(maxima.items(),key=lambda x:-x[1])[:8]},indent=2))
assert max(maxima.values())<=4096
assert not old,"inspect library warning before executing"
