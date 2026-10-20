from pathlib import Path
import re,hashlib,json
p=Path(__file__).resolve().parent
clean=lambda s:re.sub(r"^set_option (?:maxHeartbeats|maxRecDepth).*\n","",s,flags=re.M)
r=clean((p/"raw-generated/AspisR1Query31Transcript/Funs.lean").read_text()).replace("import AspisR1Query31Transcript.FunsExternal\n","")
a=(p/"sources/Query31ExplicitBoundary.lean").read_text();i=a.index("structure QueriesModel.Boundaries where");j=a.index("/--",i);decl=a[i:j].rstrip()+"\n\n"
r=r.replace("namespace AspisR1Query31Transcript\n","namespace AspisR1Query31Transcript\n\n"+decl).replace("def transcript.Transcript.queries\n","def QueriesModel.queries (B : QueriesModel.Boundaries)\n").replace("aspis_core.r0_transcript.queries_from_pairs","B.decode").replace("aspis_core.field.WideExact.from_m31","B.embed")
assert r==a
assert clean((p/"raw-generated/AspisR1Query31Transcript/Types.lean").read_text())==(p/"sources/AspisR1Query31Transcript/Types.lean").read_text()
repo=p.parents[4]
old=repo/"docs/research/100bit-spend-path-20261013/lean/bridge-opening-queries-1b98-20261017/ExtractedOpeningQueriesModel.lean"
o=old.read_text();o=o[o.index("def QueriesModel.queries"):o.index("\ndef QueriesModel.entry")];z=a[a.index("def QueriesModel.queries"):a.rindex("\nend ")];assert o==z
proof=(repo/"docs/research/100bit-spend-path-20261013/lean/ExtractedOpeningQueriesReachability.lean").read_text();proof=clean(proof).replace("import ExtractedOpeningQueriesModel","import Query31ExplicitBoundary").replace("AspisR1PublicPreparation","AspisR1Query31Transcript");assert proof==(p/"sources/Query31Success.lean").read_text()
print("PASS exact current generated owner adaptation; identical retained model body; proof reused with only import/namespace changes and resource overrides removed")
