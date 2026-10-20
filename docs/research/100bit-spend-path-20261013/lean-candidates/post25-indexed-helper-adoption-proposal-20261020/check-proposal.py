from pathlib import Path
import tempfile,subprocess,json,hashlib,shutil
p=Path(__file__).resolve().parent
j=json.loads((p/"proposal-details.json").read_text());sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(p/"sources/sampler.before.rs")==j["before_sha256"]
assert sha(p/"sources/sampler.after.rs")==j["after_sha256"]
assert sha(p/j["patch"])==j["patch_sha256"]
with tempfile.TemporaryDirectory(prefix="aspis-indexed-adoption-check-") as q:
 q=Path(q);subprocess.run(["git","init","-q",str(q)],check=True);f=q/j["target"];f.parent.mkdir(parents=True);shutil.copy(p/"sources/sampler.before.rs",f)
 subprocess.run(["git","apply","--check",str(p/j["patch"])],cwd=q,check=True)
 subprocess.run(["git","apply",str(p/j["patch"])],cwd=q,check=True)
 assert f.read_bytes()==(p/"sources/sampler.after.rs").read_bytes()
print("PASS isolated patch applies exactly; production untouched")
