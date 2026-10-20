from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
raw = (ROOT / "generated/AspisR1VariantRowSource/Funs.lean").read_text()
cut = (ROOT.parents[0] / "../../lean-candidates/s3-s9-current-repin-20261020/S3VariantRowAeneasCut.lean").resolve().read_text()

def block(text, start, end):
    i = text.index(start)
    j = text.index(end, i)
    return text[i:j]

def norm(s):
    s = s.replace("transport.Variant.row_loop.body", "row_loop_body")
    s = s.replace("transport.Variant.row_loop", "row_loop")
    s = s.replace("transport.TAU", "tau")
    s = re.sub(r"\s+", " ", s)
    return s.strip()

raw_body = block(raw, "def transport.Variant.row_loop.body", "/-- [s3_variant_row_source_cut::transport::{s3_variant_row_source_cut::transport::Variant}::row]: loop 0:")
cut_body = block(cut, "def row_loop_body", "@[rust_loop]\ndef row_loop")
assert norm(raw_body) == norm(cut_body), "row loop body differs after namespace-only normalization"

raw_loop = block(raw, "def transport.Variant.row_loop\n", "/-- [s3_variant_row_source_cut::transport::{s3_variant_row_source_cut::transport::Variant}::row]:\n    Source: 'src/transport.rs', lines 10")
cut_loop = block(cut, "def row_loop (", "def s2_row_result")
raw_loop = re.sub(r":=\s*do\s+loop", ":= loop", raw_loop)
assert norm(raw_loop) == norm(cut_loop), "row loop differs beyond single-expression do normalization/namespace"

raw_row = block(raw, "def transport.Variant.row\n", "/-- [s3_variant_row_source_cut::transport::{s3_variant_row_source_cut::transport::Variant}::coefficients")
assert "row_loop { start := 0#usize, «end» := 5#usize } j 0#usize" in norm(raw_row)
assert "row_loop { start := 0#usize, «end» := 5#usize } j 0#usize" in norm(cut)
print("PASS: extracted loop body is identical after namespace renaming; extracted loop differs only by single-expression do; S2 else initializer matches exact extracted row branch")
