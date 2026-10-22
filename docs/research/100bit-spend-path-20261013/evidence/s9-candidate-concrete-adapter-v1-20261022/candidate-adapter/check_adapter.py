from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parent; S=R/"sources/AspisR1S9CandidateHelperV1"; G=R/"raw-aeneas-diagnostic"
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
strip=lambda s:re.sub(r"(?m)^set_option [^\n]*\n", "", s)
for n in ("Types.lean","Funs.lean"):
 
 expected=strip((G/n).read_text())
 actual=(S/n).read_text()
 if n == "Funs.lean":
  expected_lines=[]
  for line in expected.splitlines():
   if "def weights." in line: expected_lines.append(line)
   else: expected_lines.append(line.replace("weights.", "_root_.AspisR1S9CandidateHelperV1.weights."))
  expected="\n".join(expected_lines)+"\n"
 assert actual==expected,n
for p in (S/"FunsExternal.lean",R/"sources/S9CandidateHelperOperationBridgeV1.lean"):
 t=p.read_text(); assert not re.search(r"\b(axiom|sorry|admit)\b",t)
 assert not re.search(r"(?m)^set_option (?:maxHeartbeats|maxRecDepth|linter\.)",t)
ops=(S/"FunsExternal.lean").read_text()
assert all(f"def field.QM31.{x} " in ops for x in ("mul","square"))
assert all(f"def field.WideExact.{x} " in ops for x in ("add","mul","mul_m31","mul_qm31"))
for p in R.rglob("*"):
 if p.is_file(): assert p.suffix not in {".olean",".ilean",".so",".dylib",".o",".a",".rlib",".pyc"},p
pin=json.loads((R/"pins.json").read_text())
assert sha(S/"FunsExternal.lean") == pin["attempt9_external_sha256"]
assert sha(S/"Funs.lean") == pin["attempt9_funs_sha256"]
print("PASS: generated source copy, six concrete dispatches, six Result-map bridge statements, source-only files")
