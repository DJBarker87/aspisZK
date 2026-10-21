#!/usr/bin/env python3
"""Audit the exact three std adapters used in the actual column extraction."""
import hashlib,json,pathlib,subprocess
HERE=pathlib.Path(__file__).resolve().parent;LEAN=HERE.parent/'lean/R1Z'
raw=subprocess.check_output(['ssh','dombarker@100.108.41.90','cat /home/dombarker/project-offloads/codex-cx-builder-ref7-20261021/columns/generated/Reference.lean'],text=True)
bank=(LEAN/'BuilderBankExtracted.lean').read_text()
a=bank.index('/-- [core::array::from_fn]');b=bank.index('/-- [core::ops::range::',a)
c=raw.index('/-- [core::array::from_fn]');d=raw.index('/-- [aspis_core::field::M31]',c)
out=(raw[:c]+bank[a:b]+raw[d:]).replace('import Aeneas\n','import R1Z.BuilderStdModels\n')
out+='\n#print axioms AspisBuilderColumnsSource.pool_v1.pair_forest_copy_builder.columns\n'
p=LEAN/'BuilderColumnsExtracted.lean';assert p.read_text()==out
assert 'axiom core.' not in out
pin=lambda s:dict(sha256=hashlib.sha256(s.encode()).hexdigest(),size=len(s.encode()))
(HERE/'builder-cont7-columns-adaptation.json').write_text(json.dumps(dict(raw=pin(raw),adapted=pin(out),
 adapters=['core.array.from_fn → BuilderStdModels.fromFn','Iterator.map.default → BuilderStdModels.iterMap','Map.Iterator.next → BuilderStdModels.mapNext'],
 trait_metadata='Remove only backend-unsupported map/collect record fields; actual next preserved',
 actual_function_bodies_unchanged=True,new_external_declarations=False),indent=2)+'\n')
