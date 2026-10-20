#!/usr/bin/env python3
"""Verify the first length fact uses the existing actual-source parser adapter."""
from pathlib import Path
import hashlib,json,importlib.util
R=Path(__file__).resolve().parents[6];B=R/'docs/research/100bit-spend-path-20261013'
old=B/'evidence/stage2-authenticated-parser-join-20261020/sources'
t=(old/'AspisR1Stage2AdoptedParseShape/Types.lean').read_text()
f=(old/'Stage2ParseShapeExplicitOps.lean').read_text().replace('import AspisR1Stage2AdoptedParseShape.Types\n','').replace('import Aeneas\n','')
expected=(t+'\n'+f).replace('AspisR1Stage2AdoptedParseShape','AspisR1Stage2ContinuationParse')
actual=(B/'lean/Stage2ContinuationParse.lean').read_text();assert actual.startswith(expected)
spec=importlib.util.spec_from_file_location('cut',B/'tools/public-serializer-extraction-kit/extract.py');cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
p=R/'crates/aspis-r1-cost-probe/src/candidate.rs';body,*_=cut.find_item(p,'pub fn parse_shape(')
pins=json.loads((B/'evidence/stage2-refactor-extraction-20261020/pins/extraction-inputs.json').read_text())
expected_hash=next(x['sha256'] for x in pins['declarations'] if x['name']=='candidate::parse_shape')
assert hashlib.sha256(body).hexdigest()==expected_hash
out=dict(parser_source_sha256=expected_hash,adapter_source='evidence/stage2-authenticated-parser-join-20261020/sources/Stage2ParseShapeExplicitOps.lean',adapter_body_exact_modulo_namespace_and_imports=True,external_operations='universally quantified ParseShapeOps; no backend axioms',scope='Parser success implies Slice.len equals successful compact.PROOF_BYTES; field canonicity and source/backend refinement remain obligations')
(B/'evidence/stage2-continuation-20261020/proofs/parse-source-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
