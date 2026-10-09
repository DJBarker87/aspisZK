#!/usr/bin/env python3
"""Generate exact field inventory and test the extracted *unchanged* Rust parser.
No fetches/build dependencies/source edits. Not Rust-to-Lean refinement.
"""
import argparse
import hashlib
import importlib.util
import json
import subprocess
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
EX = REPO / 'docs/research/v8-no-work-100-20260907/experiments'

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def extract_function(text, signature):
    start = text.index(signature)
    brace = text.index('{', start)
    depth = 1
    end = brace + 1
    while depth:
        depth += (text[end] == '{') - (text[end] == '}')
        end += 1
    return text[start:end]

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True, type=Path)
    args = ap.parse_args()
    args.out.mkdir(parents=True, exist_ok=False)
    sources = [EX / name for name in ['relation_callback.rs', 'performance_verifier.rs',
        'inactive_row_binding.rs', 'structured_weights.rs', 'auth_order.rs']]
    sources += [REPO/'crates/aspis-core/src/field.rs',
        HERE/'lean/FSV7SelectedBodyScript.lean', HERE/'lean/SameBodyOpenedTerminal.lean']
    callback = sources[0].read_text()
    assert 'const FIXED:usize=697; const Q:usize=22; const REC:usize=621; const HEAD:usize=FIXED*16+52+24;' in callback
    parse_source = extract_function(callback, "fn parse(b:&[u8])")
    assert 'if b.len()<HEAD+Q*REC || b.len()>40282 || (b.len()-HEAD-Q*REC)%52!=0' in parse_source
    fields = []
    for i in range(697):
        if i == 0:
            meaning, boundary, reader, lean = 'masked_semantic_initial_claim', 'after_C2_before_eta', 'performance_verifier::semantic w.v[0]', 'SemanticWireExecution'
            detail = {}
        elif i < 271:
            r, slot = divmod(i-1, 27)
            meaning, boundary, reader, lean = 'semantic_response_coefficient', f'before_z_{r}', 'performance_verifier::semantic w.v[1+27*r..1+27*(r+1)]', 'SemanticWireExecution'
            detail = {'round': r, 'sent_slot': slot, 'polynomial_degree': 0 if slot == 0 else slot+1, 'omitted_coefficient': 1}
        elif i < 358:
            row, lane = divmod(i-271, 29)
            meaning, boundary, reader, lean = 'component_point_claim', 'after_semantic_rounds_before_first_OOD', 'performance_verifier::semantic; inactive_row_binding::points_absorb; structured_weights::prepare', 'SameBodyOrdinary; SemanticWireExecution'
            detail = {'row': row, 'lane': lane, 'semantic_84_projection_index': 28*row+lane if lane < 28 else None, 'ordinary_scale': ['kappa','kappa^2','kappa^3'][row]}
        elif i == 358:
            meaning, boundary, reader, lean = 'inactive_claim', 'after_gamma_before_kappa', 'structured_weights::prepare w.v[358..359]', 'SameBodyOrdinary'
            detail = {'ordinary_scale': '1'}
        elif i < 417:
            row, lane = divmod(i-359, 29)
            meaning, boundary, reader, lean = 'component_OOD_answer', 'after_OOD0_before_OOD1' if row == 0 else 'after_OOD1_before_gamma', 'inactive_row_binding::to_gamma', 'SameBodyOrdinary'
            detail = {'point_ordinal': row, 'lane': lane, 'framing_byte': row}
        elif i < 441:
            r, slot = divmod(i-417, 6)
            meaning, boundary, reader, lean = 'compact_relation_response', 'after_tau_before_alpha0' if r == 0 else f'after_previous_challenges_before_alpha{r}', 'structured_weights::relation; relation_callback::compact/absorb_round', 'SameBodyCompactTerminal; SameBodyTerminalExecution'
            detail = {'round': r, 'sent_slot': slot, 'polynomial_degree': [0,1,2,3,5,6][slot], 'omitted_coefficient': 4}
        else:
            meaning, boundary, reader, lean = 'final256_coefficient', 'after_alpha0_before_queries', 'structured_weights::relation w.v[441..697]; relation_callback::query_schedule', 'SameBodyOpenedQueryUpdate.finalFromWire; SameBodyRelation.finalValues'
            detail = {'coefficient': i-441}
        fields.append(dict(index=i, byte_offset=16*i, width=16, meaning=meaning,
            canonical='four little-endian u32 limbs each < 2147483647; c0.a,c0.b,c1.a,c1.b',
            reader=reader, first_boundary=boundary, lean=lean, detail=detail,
            producer='same body parser; causal serialization source producer UNPROVED',
            theorem_status='functional algebra/projection only; literal Rust refinement NOT PROVED'))
    assert len(fields) == 697 and [x['index'] for x in fields] == list(range(697))
    other = [dict(name='C1_root',offset=11152,width=26,boundary='before_lambda_chi'),
        dict(name='C2_root',offset=11178,width=26,boundary='after_lambda_chi_before_semantic_batch'),
        dict(name='gamma_nonce',offset=11204,width=8,boundary='after_OOD1_before_gamma'),
        dict(name='alpha0_nonce',offset=11212,width=8,boundary='after_response0_before_alpha0',framing='0 byte then nonce'),
        dict(name='query_nonce',offset=11220,width=8,boundary='after_final256_before_queries'),
        dict(name='packed_records',offset=11228,width=13662,count=22,record_width=621,boundary='after_queries; queried ordinal preserved'),
        dict(name='frontiers',offset=24890,width='body.length-24890',halves='(body.length-24890)/2',node_width=26)]
    report = dict(schema='aspis-v8-fixed-field-source-producer/v2',
        revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip(),
        source_hashes={str(p.relative_to(REPO)):digest(p) for p in sources},
        sources_scope='current checkout; cfg/profile not inferred from source presence',
        fixed_fields=fields, other_sections=other,
        extracted_parser_sha256=hashlib.sha256(parse_source.encode()).hexdigest(),
        kernel_proof='NOT RUN', literal_rust_refinement='NOT PROVED',
        semantic_context='public/payment/transition/binding are independently supplied external source inputs',
        chronological_mismatches=[
            'SameBodyOpenedRun inverses precede Merkle; Rust opened_values_prepared authenticates before inversion. Pure conjunction does not prove call order.',
            'FSV7SelectedBodyScript omits packed canonicality/geometry checks; it is a Merkle suffix, not complete opened run.',
            'FSV7SelectedBodyScript hashes sorted query ordinals: matches v8_auth_order only. Without cfg, Rust hashes original ordinal then sorts entries.',
            'Whole body is available to noninteractive verifier; deriving a uniform causal prover strategy still requires source/ROM coupling, not merely parsing.'])
    (args.out/'field-source-map.json').write_text(json.dumps(report,indent=2)+'\n')
    driver = '''#![allow(dead_code)]
#[path = FIELD_PATH] mod field;
use field::QM31 as K;
const FIXED:usize=697;const Q:usize=22;const REC:usize=621;const HEAD:usize=FIXED*16+52+24;
#[derive(Debug)] enum Error{Length,Canonical}
struct Wire<'a>{v:Vec<K>,roots:([u8;26],[u8;26]),nonces:&'a[u8],records:&'a[u8],frontiers:(&'a[u8],&'a[u8])}
PARSER
fn main(){
 let mut counts=[0usize;4];
 for nodes in 0..=296 {let body=vec![0u8;24890+52*nodes];let w=parse(&body).unwrap();
  assert_eq!(w.v.len(),697);assert_eq!(w.frontiers.0.len(),26*nodes);assert_eq!(w.frontiers.1.len(),26*nodes);counts[0]+=1;}
 for size in [0,11151,24889,24891,40283,40334]{assert!(parse(&vec![0u8;size]).is_err());}
 let mut body=vec![0u8;40282];
 for i in 0..697 {let start=i*16;body[start..start+4].copy_from_slice(&1234567u32.to_le_bytes());
  let w=parse(&body).unwrap();assert_eq!(w.v[i].c0.a.0,1234567);
  assert_eq!(w.roots,([0;26],[0;26]));assert!(w.records.iter().all(|x|*x==0));
  counts[1]+=1;body[start..start+4].fill(0);
  for limb in 0..4 {let start=i*16+4*limb;body[start..start+4].copy_from_slice(&field::P.to_le_bytes());
   assert!(matches!(parse(&body),Err(Error::Canonical)));counts[2]+=1;body[start..start+4].fill(0);}}
 // Wire parse intentionally defers packed-limb canonicality.
 body[11228..11232].fill(255);let w=parse(&body).unwrap();
 assert_eq!(&w.records[..4],&[255;4]);counts[3]+=1;
 println!("PASS actual_extracted_parse admitted_lengths={} field_mutations={} noncanonical_limbs={} deferred_record_diagnostic={} malformed_lengths=6",counts[0],counts[1],counts[2],counts[3]);
}
'''.replace('FIELD_PATH',json.dumps(str(REPO/'crates/aspis-core/src/field.rs'))).replace('PARSER',parse_source)
    # Reuse the audited bounded process wrapper; do not edit its shared driver.
    spec=importlib.util.spec_from_file_location('scoped_checker',HERE/'check.py')
    checker=importlib.util.module_from_spec(spec);spec.loader.exec_module(checker)
    with tempfile.TemporaryDirectory(prefix='aspis-source-parser-') as temp:
        temp=Path(temp); rust=temp/'parser.rs';rust.write_text(driver)
        report['generated_driver_sha256']=digest(rust)
        report['checks']=[checker.run('parser-rustc',['rustc','--edition=2021','-O',str(rust),'-o',str(temp/'parser')],REPO,args.out,timeout=90)]
        if report['checks'][0]['exit_code']==0:
            report['checks'].append(checker.run('parser-execute',[str(temp/'parser')],REPO,args.out,timeout=30))
    report['test_scope']='actual verbatim extracted parse with actual field.rs; synthetic bytes; not Lean/source semantic refinement or full verifier'
    (args.out/'report.json').write_text(json.dumps({k:v for k,v in report.items() if k!='fixed_fields'},indent=2)+'\n')
    return 0 if len(report['checks'])==2 and all(x['exit_code']==0 for x in report['checks']) else 2

if __name__=='__main__':
    raise SystemExit(main())
