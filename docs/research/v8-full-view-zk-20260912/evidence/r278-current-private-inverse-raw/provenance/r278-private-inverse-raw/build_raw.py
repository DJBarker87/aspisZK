"""Copy the three selected R276 Lean declarations verbatim into R278 raw adapter."""
import hashlib, json, pathlib

ROOT = pathlib.Path(__file__).resolve().parent
SOURCE = ROOT.parent / "r276-private-inverse-leaf-translation/generated/AspisR276PrivateInverseLeaves/Funs.lean"
OUT = ROOT / "AspisR278PrivateInverseRaw.lean"
EXPECTED_SOURCE = "3e3a3ee0630af9de63601a448c2a240e0f31fc6712de6def854c72de1e6b0269"
sha = lambda b: hashlib.sha256(b).hexdigest()
source_bytes = SOURCE.read_bytes()
assert sha(source_bytes) == EXPECTED_SOURCE, sha(source_bytes)
source = source_bytes.decode()

NAMES = [
    "circle_norm.joined_inverse.line_norm.r110_norm.B.ZERO",
    "circle_norm.joined_inverse.line_norm.r110_norm.B.neg",
    "circle_norm.joined_inverse.line_norm.r110_norm.B.inv",
]

def copied_block(name):
    marker = "def " + name
    at = source.index(marker)
    start = source.rfind("/--", 0, at)
    assert start >= 0
    stops = [p for p in (source.find("\n/--", at), source.find("\nend AspisR276PrivateInverseLeaves", at)) if p >= 0]
    stop = min(stops)
    block = source[start:stop].rstrip()
    assert block.endswith("\n" + source[at:stop].splitlines()[0]) or "def " + name in block
    return block

blocks = [copied_block(n) for n in NAMES]
header = """import Aeneas.Std
import AspisR249R110Raw
import AspisR156FullFreeze.FunsCore
open Aeneas Aeneas.Std Result ControlFlow Error
open AspisR249R110Raw AspisR156FullFreeze
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

noncomputable section
namespace AspisR278PrivateInverseRaw

"""
footer = """

#print axioms circle_norm.joined_inverse.line_norm.r110_norm.B.ZERO
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.B.neg
#print axioms circle_norm.joined_inverse.line_norm.r110_norm.B.inv

end AspisR278PrivateInverseRaw
"""
OUT.write_text(header + "\n\n".join(blocks) + footer)
report = {
    "source_path": str(SOURCE.relative_to(ROOT.parents[1])),
    "source_sha256": sha(source_bytes),
    "output_path": OUT.name,
    "output_sha256": sha(OUT.read_bytes()),
    "copied_declarations": [
        {"name": n, "exact_source_block_sha256": sha(block.encode()), "replacement_count": 0,
         "block_is_exact_source_substring": block in source}
        for n, block in zip(NAMES, blocks)
    ],
    "body_or_type_replacements": 0,
    "compiled": False,
}
(ROOT / "raw-adapter.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
