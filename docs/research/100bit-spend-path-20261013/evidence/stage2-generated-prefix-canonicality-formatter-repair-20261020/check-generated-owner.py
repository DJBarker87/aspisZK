from pathlib import Path
import re
p=Path(__file__).resolve().parent
def clean(s):
 s=re.sub(r"^set_option (?:maxHeartbeats|maxRecDepth).*\n","",s,flags=re.M)
 s=re.sub(r"^-- removed generator .*\n","",s,flags=re.M)
 return s
for raw,adapted in [("Funs","GeneratedFuns"),("Types","GeneratedTypes")]:
 a=clean((p/"raw-generated"/(raw+".lean")).read_text())
 b=clean((p/"sources"/(adapted+".lean")).read_text())
 if raw=="Types":
  comment="-- Candidate namespace-collision adapter: the generated functions do not inspect Error discriminants."
  assert b.count(comment)==1
  assert "read_discriminant" not in (p/"raw-generated/Funs.lean").read_text()
  b=b.replace(comment,"@[discriminant isize]")
 assert a==b
print("PASS generated function bodies unchanged; resource options removed; unused Error-discriminant instance omission checked")
