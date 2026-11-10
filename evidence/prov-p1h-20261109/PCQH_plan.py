#!/usr/bin/env python3
"""PCQH_plan.py: write PCQH_PLAN.json (generator passes against the OFF emissions of this job)."""
import json
from pathlib import Path
H=Path(__file__).resolve().parent
NFN_P2=["verifier.QueryGeometry.for_range","verifier.QueryGeometry.for_range_loop0","verifier.QueryGeometry.for_range_loop0.body","verifier.QueryGeometry.for_range_loop0_loop0","verifier.QueryGeometry.for_range_loop0_loop0.body","verifier.batch_prefix_products","verifier.batch_prefix_products_loop","verifier.batch_prefix_products_loop.body"]
FIELD=["field.reduce_u64","field.M31.add","field.M31.sub","field.M31.mul","field.M31.reduce_u64","field.M31.double","field.CM31.add","field.CM31.sub","field.CM31.mul","field.mul_by_r"]
def ps(tag,fresh_dir,ns,run,gate,gns,only,**kw):
    d=dict(tag=tag,kind='Funs',fresh_dir=fresh_dir,fresh_ns=ns,run=run,gate=gate,gate_types=gate,gate_namespace=gns,gns=gns,name_map={},rename_fresh=[],gate_extra=[],only_fresh=only)
    d.update(kw);return d
P={}
P['NFN_ExtractedGeometry']=dict(passes=[
 ps('_h1','prov-p1h-20261109/PCQH_E001_emitted/raw/PCQH_h07','PCQH_h07','PCQH_E001','prov-p2f-20261109/inputs/gate_NFN_ExtractedGeometry.lean','NEW_GeometryActual',NFN_P2,extra_import=['PRVH_WrapAdd'],fresh_prelude='inputs/NFN_shr_prelude.lean',given='inputs/NFN_h1_given.json'),
 ps('_h2','prov-p1h-20261109/PCQH_E003_emitted/raw/PCQH_hf1','PCQH_hf1','PCQH_E003','prov-p2f-20261109/inputs/gate_NFN_ExtractedGeometry.lean','NEW_GeometryActual',['aspis_core.'+x for x in FIELD if x!='field.mul_by_r'],rename_fresh=['field.=aspis_core.field.'],extra_import=['PRVH_WrapAdd'])])
P['NJA_CountBody']=dict(passes=[ps('_h1','prov-p1h-20261109/PCQH_E002_emitted/raw/PCQH_h09','PCQH_h09','PCQH_E002','prov-p2d-20261109/inputs/gate_NJA_CountBody.lean','NJA_Multiproof',["multiproof.node_count_loop0","multiproof.node_count_loop0.body","multiproof.node_count_loop0_loop0","multiproof.node_count_loop0_loop0.body","multiproof.node_count_loop0_loop0_loop0","multiproof.node_count_loop0_loop0_loop0.body"],extra_import=['PRVH_WrapAdd'])])
P['FIn_WeightsFuns']=dict(passes=[ps('_h1','prov-p1h-20261109/PCQH_E003_emitted/raw/PCQH_hf1','PCQH_hf1','PCQH_E003','prov-p5-20261109/inputs/gate_FIn_WeightsFuns.lean','FIn_WeightsExtract',FIELD,extra_import=['PRVH_WrapAdd'])])
P['RPz7_FIo_NativeFuns']=dict(passes=[ps('_h1','prov-p1h-20261109/PCQH_E003_emitted/raw/PCQH_hf1','PCQH_hf1','PCQH_E003','prov-p2a-20261109/gate_src/RPz7_FIo_NativeFuns.lean','FIo_Native',['aspis_core.field.reduce_u64'],rename_fresh=['field.=aspis_core.field.'],extra_import=['PRVH_WrapAdd'])])
(H/'PCQH_PLAN.json').write_text(json.dumps(P,indent=1)+'\n')
