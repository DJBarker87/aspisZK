#!/usr/bin/env python3
"""PCQH extraction specs (P1h): overflow-checks OFF emissions for wrapping-configuration gate definitions."""
import json,sys
from pathlib import Path
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
CP='private-leaf-salts,optimized-terminal,program-build'
C={'cp':dict(crate='aspis-r1-cost-probe',manifest='crates/aspis-r1-cost-probe/Cargo.toml',features=CP),
   'core':dict(crate='aspis-core',manifest='crates/aspis-core/Cargo.toml',features='r0')}
S=[]
def add(sid,c,label,roots,opaque=(),include=(),modules=(),basis='',tool='extended'):
    S.append(dict(spec_id=sid,kind='frozen-OFF',label=label,start_from=list(roots),include=list(include),opaque=list(opaque),namespace='PCQH_'+sid.lower(),aeneas_tool=tool,covers=dict(modules=list(modules)),basis=basis,**C[c]))
P=['aspis_core::field::P']
add('H07','cp','OFF: verifier QueryGeometry::for_range, batch_prefix_products (D07 shape)',['crate::verifier::_::for_range','crate::verifier::batch_prefix_products'],include=P,modules=['NFN_ExtractedGeometry','Port3_NativeGeometryBody','Port4C_NativePrefix'])
add('H09','cp','OFF: multiproof::node_count (D09 shape)',['crate::multiproof::node_count'],include=P,modules=['NJA_CountBody'])
add('HF1','core','OFF: aspis-core field arithmetic (PCQF NEW1 roots)',['crate::field::reduce_u64','crate::field::_::reduce_u62','crate::field::_::reduce_u64','crate::field::_::ZERO','crate::field::_::ONE','crate::field::_::new','crate::field::_::from_m31','crate::field::_::add','crate::field::_::sub','crate::field::_::mul','crate::field::_::square','crate::field::_::mul_m31','crate::field::_::double','crate::field::_::from_cm31'],modules=['FIn_WeightsFuns','NFN_ExtractedGeometry','RPz7_FIo_NativeFuns'])
(E/'PCQH_extract_specs.json').write_text(json.dumps(dict(schema='PCQH_extract_specs/1',specs=S),indent=1)+'\n')
