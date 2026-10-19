from pathlib import Path
import re, hashlib
p=Path(__file__).resolve().parent
for name in ["Types","Funs"]:
 raw=(p/"raw-generated/AspisR1Post25Sampler"/(name+".lean")).read_text()
 clean=re.sub(r"^set_option (?:maxHeartbeats|maxRecDepth).*\n","",raw,flags=re.M)
 clean=re.sub(r"^/\- You can set the `max(?:Heartbeats|RecDepth)`.*\n", "", clean, flags=re.M)
 assert [x for x in clean.splitlines() if x.strip()]==[x for x in (p/"sanitized-sources"/(name+".lean")).read_text().splitlines() if x.strip()]
print("PASS: generated owner body retained, generated resource options removed")
