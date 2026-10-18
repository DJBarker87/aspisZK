from pathlib import Path
import hashlib, json
root = Path(__file__).resolve().parent
for name in ["Types", "Funs"]:
    canonical = (root / ("canonical-" + name + ".lean")).read_bytes()
    extended = (root / ("extended-" + name + ".lean")).read_bytes()
    common = canonical.removesuffix(b"end AspisR1PublicPreparation\n")
    assert extended.startswith(common), name
    print(name, len(common), hashlib.sha256(extended).hexdigest())
