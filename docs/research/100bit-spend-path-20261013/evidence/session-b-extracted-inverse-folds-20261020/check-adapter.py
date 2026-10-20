from pathlib import Path
import re,json,hashlib
p=Path(__file__).resolve().parent
clean=lambda s:re.sub(r"^set_option (?:maxHeartbeats|maxRecDepth).*\n","",s,flags=re.M)
assert clean((p/"raw-generated/Types.lean").read_text())==(p/"sources/AspisR1FoldInverses/Types.lean").read_text()
f=clean((p/"raw-generated/Funs.lean").read_text()).replace("import AspisR1FoldInverses.FunsExternal\n","")
selected=(p/"sources/FoldInversesExplicitOps.lean").read_text()
a=selected.index("structure FoldOps where");b=selected.index("/--",a);ops=selected[a:b].rstrip()+"\n\n"
f=f.replace("namespace AspisR1FoldInverses\n","namespace AspisR1FoldInverses\n\n"+ops)
for n in ["circle_fold_with_inverses","line_fold_with_inverses"]:f=f.replace("def verifier."+n+"\n","def verifier."+n+"\n  (ops : FoldOps)\n")
for a,b in [("aspis_core.field.WideExact.add","ops.add"),("aspis_core.field.WideExact.sub","ops.sub"),("aspis_core.field.WideExact.mul_m31","ops.scale"),("aspis_core.field.WideExact.mul","ops.mul"),("aspis_core.field.M31.mul","ops.baseMul")]:f=f.replace(a,b)
assert f==selected
pins=json.loads((p/"rust-kit/source-pins.json").read_text())
for cut in pins["cuts"]:
 q=p/"rust-kit/fragments"/(cut["name"]+".rs");s=q.read_text().removesuffix("\n");assert hashlib.sha256(s.encode()).hexdigest()==cut["sha256"];assert s in (p/"rust-kit/lib.rs").read_text()
print("PASS exact generated helper bodies under explicit field operation parameters and frozen Rust body pins")
