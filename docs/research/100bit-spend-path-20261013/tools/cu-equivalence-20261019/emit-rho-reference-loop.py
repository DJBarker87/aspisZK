#!/usr/bin/env python3
"""Promote only the complete original coefficient loop, without opaque templates."""
from pathlib import Path
import argparse,hashlib,json,re
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
here=Path(__file__).resolve().parent;area=here.parents[1];sha=lambda b:hashlib.sha256(b).hexdigest()
raw=(here/'rho-coefficients-generated/Funs.lean').read_bytes();header,*chunks=re.split(rb'(?m)(?=^/--)',raw)
selected=[c for c in chunks if re.search(rb'def rho_old\.coefficients',c)]
assert len(selected)==3
out=header.replace(b'AspisR1RhoCoefficients.Types',b'AspisR1RhoReferenceLoop.Types').replace(b'AspisR1RhoCoefficients.FunsExternal',b'AspisR1RhoReferenceLoop.FunsExternal')+b''.join(selected)+b'end AspisR1RhoCoefficients\n'
types=b'''import AspisR1RhoDiagnostics.Types
namespace AspisR1RhoCoefficients
abbrev aspis_core.field.M31 := AspisR1CuRho.field.M31
abbrev aspis_core.field.CM31 := AspisR1CuRho.field.CM31
abbrev aspis_core.field.QM31 := AspisR1CuRho.field.QM31
abbrev aspis_core.field.WideExact := AspisR1CuRho.field.WideExact
abbrev BatchedWeights := AspisR1CuRho.verifier.BatchedWeights
end AspisR1RhoCoefficients
'''
# The aliased nominal carriers have exactly the emitted fields, up to prefixes.
raw_types=(here/'rho-coefficients-generated/Types.lean').read_text()
existing=(area/'lean/AspisR1CuRho/Types.lean').read_text()+(area/'lean/AspisR1RhoDiagnostics/Types.lean').read_text()
for local,original in [('aspis_core.field.CM31','field.CM31'),('aspis_core.field.QM31','field.QM31'),('aspis_core.field.WideExact','field.WideExact'),('BatchedWeights','verifier.BatchedWeights')]:
 pattern=lambda name:r'structure '+re.escape(name)+r' where\n(?:  [^\n]+\n)+'
 a=re.search(pattern(local),raw_types)[0];b=re.search(pattern(original),existing)[0]
 assert a.replace('aspis_core.field.','field.').replace('structure BatchedWeights','structure verifier.BatchedWeights')==b
outputs={'Types.lean':types,'Funs.lean':out}
for name,b in outputs.items():
 p=area/'lean/AspisR1RhoReferenceLoop'/name
 if args.check:assert p.read_bytes()==b,name
 else:p.parent.mkdir(exist_ok=True);p.write_bytes(b)
meta=dict(raw_funs_sha256=sha(raw),raw_types_sha256=sha(raw_types.encode()),promoted={n:sha(b) for n,b in outputs.items()},retained_body_sha256=[sha(c) for c in selected],scope='Three entire emitted rho_old.coefficients declarations. No reborrow/new-loop template or stub function is imported. Shared byte-identical carrier fields are reused by aliases; imports adjusted only, retained function bodies unchanged.')
p=here/'rho-reference-loop-layout.json';b=(json.dumps(meta,indent=2)+'\n').encode()
if args.check:assert p.read_bytes()==b
else:p.write_bytes(b)
print(json.dumps(dict(check=args.check,whole_reference_loop_bodies_unchanged=True)))
