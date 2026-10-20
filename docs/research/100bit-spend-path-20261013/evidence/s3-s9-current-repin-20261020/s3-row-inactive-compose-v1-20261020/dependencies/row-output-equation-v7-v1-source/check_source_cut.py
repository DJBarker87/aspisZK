#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re, sys
root = Path(__file__).resolve().parent
sources = root / 'sources'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def body(path, name):
    text = path.read_text()
    m = re.search(rf'^def {re.escape(name)} \(j : Nat\) : Nat :=\n((?:[ \t]+[^\n]*\n)+)', text, re.M)
    if not m: raise SystemExit(f'missing declaration {name} in {path}')
    return re.sub(r'\s+', ' ', m.group(1)).strip()
model = body(sources / 'S3S9CurrentSourceModel.lean', 's2Row')
cut = body(sources / 'S3VariantRowPrefixFormula.lean', 's2Row_source_cut')
formula = body(sources / 'S3VariantRowPrefixFormula.lean', 'rowFormula')
if model != cut: raise SystemExit('source-cut body differs from original s2Row declaration')
if model != formula: raise SystemExit('rowFormula differs from original s2Row declaration')
report = {
  'status':'pass',
  'source_model_sha256':sha(sources/'S3S9CurrentSourceModel.lean'),
  'formula_module_sha256':sha(sources/'S3VariantRowPrefixFormula.lean'),
  'matched_declaration':'AspisR1.S3S9CurrentSourceModel.s2Row',
  'cut_declaration':'AspisR1.S3S9CurrentSourceModel.s2Row_source_cut',
  'comparison':'whitespace-normalized RHS bytes are identical for both the copied source-cut definition and the row formula'
}
print(json.dumps(report, indent=2))
