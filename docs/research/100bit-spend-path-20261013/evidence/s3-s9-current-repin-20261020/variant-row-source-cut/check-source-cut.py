from pathlib import Path
import hashlib,json,sys
B=Path(__file__).resolve().parent
P=json.loads((B/"input/source-pins.json").read_text())
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for original,expected in P["upstream_source_sha256"].items():
    if original.endswith("mod.rs"): continue
    copied={
      "crates/aspis-r1-cost-probe/src/transport.rs":"input/src/transport.rs",
      "crates/aspis-core/src/r0/transport.rs":"input/src/aspis_core/r0/transport.rs",
      "crates/aspis-core/src/r0/transport_pads.rs":"input/src/aspis_core/r0/transport_pads.rs"
    }[original]
    assert H(B/copied)==expected,(original,copied)
assert "pub type Message<E> = [E; MESSAGE_LEN];" in Path("crates/aspis-core/src/r0/mod.rs").read_text()
for rel,expected in P["kit_file_sha256"].items():
    if rel.startswith("source-pins/"): continue
    assert H(B/"input"/rel)==expected,rel
print(json.dumps({"status":"source-cut-green","pins":P["upstream_source_sha256"]},indent=2))
