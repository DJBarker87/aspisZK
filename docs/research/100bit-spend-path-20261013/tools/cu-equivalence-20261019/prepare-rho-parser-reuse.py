#!/usr/bin/env python3
"""Reuse checked strict-parser proof bodies with explicit declaration transport."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,re,subprocess,tempfile
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args()
here=Path(__file__).resolve().parent;area=here.parents[1];repo=here.parents[4];old=area/'lean/extracted-decode-k-canonicality-20261018';sha=lambda b:hashlib.sha256(b).hexdigest()
parser=area/'tools/public-serializer-extraction-kit/extract.py';spec=importlib.util.spec_from_file_location('cut',parser);cut=importlib.util.module_from_spec(spec);spec.loader.exec_module(cut)
field='crates/aspis-core/src/field.rs';candidate='16a39d2a8a5124e25c787f2b9fcaf8449fb84611';baseline=subprocess.check_output(['git','-C',str(repo),'rev-parse','b302c0d49'],text=True).strip()
anchors=['pub fn from_le_bytes(bytes: [u8; 4])','pub fn from_le_bytes(bytes: &[u8]) -> Option<CM31>','pub fn from_le_bytes(bytes: &[u8]) -> Option<QM31>']
source_pins=[]
for revision in [baseline,candidate,candidate+'^']:
 raw=subprocess.check_output(['git','-C',str(repo),'show',revision+':'+field]);parts=[]
 with tempfile.NamedTemporaryFile() as f:
  f.write(raw);f.flush()
  for anchor in anchors:
   body,*_=cut.find_item(Path(f.name),anchor);parts.append(sha(body))
 source_pins.append(dict(revision=revision,field_sha256=sha(raw),parser_body_sha256=parts))
assert all(x['parser_body_sha256']==source_pins[0]['parser_body_sha256'] for x in source_pins)
raw=(old/'AspisR1DecodeKFullV10/Funs.lean').read_bytes();_,*chunks=re.split(rb'(?m)(?=^/--)',raw)
names=['core.option.Option.ok_or','core.option.Option.Insts.CoreOpsTry_traitTry.branch','core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual','aspis_core.field.M31.from_le_bytes','aspis_core.field.CM31.from_le_bytes','aspis_core.field.QM31.from_le_bytes']
selected=[]
for name in names:
 c=next(c for c in chunks if re.search(rb'(?m)^def\s+'+re.escape(name.encode())+rb'(?:\s|$)',c))
 selected.append(c)
body=b''.join(selected).replace(b'aspis_core.field.',b'field.')
# Registration metadata is unused by these direct proof calls; avoid duplicate
# global source-name registrations when the original source root is imported.
body=re.sub(rb'@\[rust_fun\s+"[^"]*"\]\n',b'',body)
assert b'@[rust_' not in body
funs=b'''-- Existing strict parser bodies, declaration-path transport only.
import AspisR1RhoDiagnostics.Funs
import DecodeKOptionDiscriminantBridge
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
namespace AspisR1CuRho
'''+body+b'\nend AspisR1CuRho\n'
outputs={'AspisR1RhoParser/Funs.lean':funs}
proofs={
 'CuSavingsRhoParserM31.lean':'AspisR1DecodeKFullV10ParserCanonicality.lean',
 'CuSavingsRhoParserCanonicality.lean':'AspisR1DecodeKFullParserCanonicalityCMQ.lean'}
transport={
 'import AspisR1DecodeKFullV10.Funs':'import AspisR1RhoParser.Funs',
 'import AspisR1DecodeKFullV10ParserCanonicality':'import CuSavingsRhoParserM31',
 'AspisR1DecodeKFullV10ParserCanonicality':'AspisR1.CuSavingsRhoParserM31',
 'AspisR1DecodeKFullParserCanonicality':'AspisR1.CuSavingsRhoParserCanonicality',
 'AspisR1DecodeKFullV10.aspis_core.field.':'AspisR1CuRho.field.',
 'AspisR1DecodeKFullV10.core.option.':'AspisR1CuRho.core.option.'}
for name,original in proofs.items():
 s=(old/original).read_text()
 for before,after in transport.items():s=s.replace(before,after)
 outputs[name]=s.encode()
meta=dict(baseline=baseline,candidate=candidate,source_parser_identity=source_pins,
 inherited_funs_sha256=sha(raw),shared_option_bridge=dict(source=str((old/'DecodeKOptionDiscriminantBridge.lean').relative_to(repo)),sha256=sha((old/'DecodeKOptionDiscriminantBridge.lean').read_bytes())),selected_declarations=names,raw_selected_body_sha256=[sha(c) for c in selected],
 inherited_proofs={n:sha((old/o).read_bytes()) for n,o in proofs.items()},
 promoted_sha256={n:sha(b) for n,b in outputs.items()},proof_identifier_transport=transport,
 scope='Reuse original checked parser source and proof bodies. Declaration-prefix/import changes only; remove unconsumed rust_fun registrations. Reuse identical current carriers/modulus through diagnostics; no enum or opaque template is imported. Reader/caller composition remains separate.')
for name,b in outputs.items():
 p=area/'lean'/name
 if a.check:assert p.read_bytes()==b,name
 else:p.parent.mkdir(exist_ok=True);p.write_bytes(b)
p=here/'rho-parser-reuse.json';b=(json.dumps(meta,indent=2)+'\n').encode()
if a.check:assert p.read_bytes()==b
else:p.write_bytes(b)
print(json.dumps(dict(check=a.check,parser_source_identical=True,proof_identifier_transport_only=True)))
