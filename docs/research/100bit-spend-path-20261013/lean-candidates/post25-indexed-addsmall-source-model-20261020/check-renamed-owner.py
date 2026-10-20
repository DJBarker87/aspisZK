from pathlib import Path
import json,re
p=Path(__file__).resolve().parent
j=json.loads((p/"worker-manifest.json").read_text())
for m in j["proof_modules"][:2]:
 n=m["module"].split(".")[-1]
 raw=(p/"extraction/candidate-generated/AspisR1Post25Sampler"/(n+".lean")).read_text()
 x=re.sub(r"^set_option (?:maxHeartbeats|maxRecDepth).*\n","",raw,flags=re.M)
 x=re.sub(r"^/\- You can set the `(?:maxHeartbeats|maxRecDepth)`.*\n","",x,flags=re.M).replace("AspisR1Post25Sampler","AspisR1Post25SamplerIndexedAddSmallCandidate")
 assert x==(p/m["source"]).read_text(),n
print("PASS generated owner: namespace rename and removal of resource options/comments only")
