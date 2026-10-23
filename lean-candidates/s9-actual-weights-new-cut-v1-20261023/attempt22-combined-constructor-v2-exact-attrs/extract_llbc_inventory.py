"""Emit a compact declaration inventory from Charon LLBC without retaining LLBC."""
import hashlib, json, sys
from pathlib import Path
source = Path(sys.argv[1])
llbc = Path(sys.argv[2])
output = Path(sys.argv[3])
obj = json.loads(llbc.read_text())
rows = []
for fn in obj["translated"]["fun_decls"]:
    if not isinstance(fn, dict):
        continue
    meta = fn.get("item_meta") or {}
    text = meta.get("source_text") or ""
    if "weights_new" in text or "box_from_parts" in text:
        rows.append({
            "name": meta.get("name"),
            "opacity": meta.get("opacity"),
            "span": meta.get("span"),
            "source_text_sha256": hashlib.sha256(text.encode()).hexdigest(),
        })
assert any(r["opacity"] == "Transparent" and "box_from_parts" in str(r["name"]) for r in rows)
assert any(r["opacity"] == "Transparent" and "weights_new" in str(r["name"]) for r in rows)
result = {
    "source_packet": str(source),
    "llbc_sha256": hashlib.sha256(llbc.read_bytes()).hexdigest(),
    "llbc_bytes": llbc.stat().st_size,
    "has_errors": obj.get("has_errors"),
    "total_fun_decls": len(obj["translated"]["fun_decls"]),
    "target_declarations": rows,
    "raw_llbc_retained": False,
}
output.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
