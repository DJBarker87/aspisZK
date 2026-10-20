from pathlib import Path
import re,json,hashlib
p=Path(__file__).resolve().parent
clean=lambda s:re.sub(r"^set_option (?:maxHeartbeats|maxRecDepth).*\n","",s,flags=re.M)
assert clean((p/"raw-generated/Types.lean").read_text())==(p/"sources/AspisR1GammaCaller/Types.lean").read_text()
f=clean((p/"raw-generated/Funs.lean").read_text()).replace("import AspisR1GammaCaller.FunsExternal\n","")
selected=(p/"sources/GammaCallerExplicitHelpers.lean").read_text();a=selected.index("structure GammaHelpers where");b=selected.index("/--",a);ops=selected[a:b].rstrip()+"\n\n"
f=f.replace("namespace AspisR1GammaCaller\n","namespace AspisR1GammaCaller\n\n"+ops).replace("def sampler.gamma_sample\n","def sampler.gamma_sample\n  (ops : GammaHelpers)\n")
f=f.replace("sampler.low_base_p_digits block","ops.low block").replace("sampler.add_small_base_p","ops.add").replace("sampler.decode8","ops.decode")
assert f==selected
pins=json.loads((p/"rust-kit/source-pins.json").read_text())
for cut in pins["cuts"]:
 q=p/"rust-kit/fragments"/(cut["name"]+".rs");s=q.read_text().removesuffix("\n");assert hashlib.sha256(s.encode()).hexdigest()==cut["sha256"];assert s in (p/"rust-kit/lib.rs").read_text()
print("PASS exact generated gamma caller under explicit helper parameters and frozen Rust body pin")
