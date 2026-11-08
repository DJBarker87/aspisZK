from pathlib import Path
import lzma,json
P=Path("/home/dombarker/project-offloads/codex-pv-lib-spec-20261107/evidence")
r=[json.loads(l.split("NEP62_RESULT ",1)[1]) for l in (P/"out-49792-w3.log").read_text().splitlines() if l.startswith("NEP62_RESULT ")]
files=[P/"raw-audit"/("NEP_pv-thread_"+v["root"]+"_REACHABLE.txt") for v in r]
assert len(files)==27 and all(f.exists() for f in files)
(P/"SESSION3_RAW_GRAPH_ARCHIVE.json.xz").write_bytes(lzma.compress(json.dumps({f.name:f.read_text() for f in files},sort_keys=True).encode()))
