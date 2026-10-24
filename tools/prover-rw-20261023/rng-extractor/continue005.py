"""One-time candidate005 repair; retain all historical sources and binaries."""
from pathlib import Path
import hashlib,json,shutil
D=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/rng-extractor')
pin=lambda p:dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
archive=D/'candidate-003';archive.mkdir()
b=D/'base/src/_build/default/main.exe'
assert pin(b)['sha256']=='09af4fe5a40f2340b3b326e01b15b23d8e8a0a39e3ae25938f9033dd56d5fdc5'
shutil.copy2(b,archive/'main.exe')
for name in ['candidate-003.patch','candidate-003-source-manifest.json','candidate-004.patch','candidate-004-source-manifest.json','candidate-pins.json']:
    shutil.copy2(D/name,archive/name)
p=D/'base/src/llbc/TypesAnalysis.ml';s=p.read_text()
a=s.index('      match def.item_meta.name with');z=s.index('\n    in\n    !Config.use_tuple_structs',a)
s=s[:a]+'''      List.exists
        (fun path -> def.item_meta.name = Charon.TypesUtils.to_name path)
        [ ["core"; "num"; "niche_types"; "NonZeroI32Inner"];
          ["core"; "num"; "nonzero"; "NonZero"];
          ["getrandom"; "error"; "Error"] ]'''+s[z:]
p.write_text(s)
print('Preserved binary003; repaired complete typed-name equality without flattening')
