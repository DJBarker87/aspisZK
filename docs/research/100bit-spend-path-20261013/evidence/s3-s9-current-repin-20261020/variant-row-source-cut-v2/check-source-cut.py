from pathlib import Path
import hashlib,json
B=Path(__file__).resolve().parent
P=json.loads((B/"input/source-pins.json").read_text())
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
copy={"crates/aspis-r1-cost-probe/src/transport.rs":"input/src/transport.rs","crates/aspis-core/src/r0/transport.rs":"input/aspis-core/src/r0/transport.rs","crates/aspis-core/src/r0/transport_pads.rs":"input/aspis-core/src/r0/transport_pads.rs"}
for original,rel in copy.items(): assert H(B/rel)==P["upstream_source_sha256"][original],original
for rel,expected in P["kit_file_sha256"].items():
 if rel.startswith("source-pins/"): continue
 assert H(B/"input"/rel)==expected,rel
mod=Path("crates/aspis-core/src/r0/mod.rs").read_text()
assert "pub const MESSAGE_LEN: usize = 1024;" in mod
assert "pub type Message<E> = [E; MESSAGE_LEN];" in mod
print(json.dumps({"status":"source-cut-green","pins":P["upstream_source_sha256"]},indent=2))
