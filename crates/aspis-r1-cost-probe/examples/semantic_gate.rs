//! UNPROVED COST PROBE: native byte-equality evidence against S4 semantics.
use aspis_core::{field::{WideExact as E, QM31}, state_only_prefix::r0 as sw};
use aspis_prover::HOST_HASH;
use aspis_r1_cost_probe::{sampler, semantic, semantic_wire};
use serde_json::json;
use sha2::{Digest, Sha256};
use std::path::Path;

fn hex(b: &[u8]) -> String { b.iter().map(|v| format!("{v:02x}")).collect() }
fn kbytes(x: QM31) -> [u8; 32] { E::from_qm31(x).to_le_bytes() }
fn main() {
    let args: Vec<_> = std::env::args().collect();
    let fixture_dir = Path::new(&args[1]);
    let out = Path::new(&args[2]);
    assert!(!out.exists(), "unchanged gate output must not be overwritten");
    let mut blocks = vec![[0u8; 32], [255u8; 32]];
    for bit in 0..256 {
        let mut b = [0; 32]; b[bit/8] = 1 << (bit%8); blocks.push(b);
        let mut c = [255; 32]; c[bit/8] ^= 1 << (bit%8); blocks.push(c);
    }
    for n in 0..4096u32 { blocks.push(Sha256::digest(n.to_le_bytes()).into()); }
    let mut sampler_digest = Sha256::new();
    for block in &blocks {
        let a = sampler::qm31_sample(block);
        assert_eq!(kbytes(a), kbytes(aspis_core::r0_transcript::qm31_sample(block)));
        sampler_digest.update(kbytes(a));
        for row in [sampler::CircleRow::First, sampler::CircleRow::Second] {
            assert_eq!(sampler::circle_sample(block,row), aspis_core::r0_transcript::circle_sample(block,row));
        }
    }
    let mut fixtures = vec![];
    for name in ["transfer", "withdrawal"] {
        let proof = std::fs::read(fixture_dir.join(format!("{name}.proof.bin"))).unwrap();
        let public_bytes = std::fs::read(fixture_dir.join(format!("{name}.public.bin"))).unwrap();
        let statement = aspis_statement::pool_v1::decode_pool_v1_pair_forest_terminal_statement_v1(&public_bytes).unwrap();
        let public = aspis_prover::r0_fixture::statement_public(&statement);
        let prefix = &proof[..aspis_statement::r0::SEMANTIC_BYTES];
        let old = aspis_statement::state_only_verify::r0::verify_semantics_heap(public,prefix,HOST_HASH).unwrap();
        let new = semantic::verify(public,prefix,HOST_HASH).unwrap();
        assert_eq!(new.roots,[old.c1_root,old.c2_root]);
        assert_eq!(new.challenges.with_alphas(&new.alpha),old.challenges.with_alphas(&old.alpha));
        assert_eq!(new.alpha,old.alpha);
        for p in 0..3 { for l in 0..29 {
            assert_eq!(kbytes(new.claims[p][l]),old.claims[p][l].to_le_bytes());
        }}
        for l in 0..29 { assert_eq!(kbytes(new.before_z1[l]),old.before_z1[l].to_le_bytes()); }
        assert_eq!(new.state_before_z0,old.state_before_z0);
        assert_eq!(new.z,old.z);
        assert_eq!(new.transcript.state(),old.transcript.state());
        assert_eq!(new.transcript.next_row(),old.transcript.next_row());
        let original_prefix = sw::Prefix::parse(prefix).unwrap();
        let probe_prefix = semantic_wire::Prefix::parse(prefix).unwrap();
        let mut t = sw::SemanticTranscript::new(HOST_HASH,&public.public_bytes().unwrap(),original_prefix.c1_root).unwrap();
        let mut pt = semantic_wire::SemanticTranscript::new(HOST_HASH,&public.public_bytes().unwrap(),probe_prefix.c1_root).unwrap();
        let mut fields = Vec::new();
        let mut transcript_states = Vec::new();
        let mut polynomial_values = 0;
        let mut running = sw::decode_values::<1>(14,original_prefix.payload(14).unwrap()).unwrap()[0];
        for row in 0..25u8 {
            let x = t.semantic(row,original_prefix.record(row).unwrap()).unwrap();
            let px = pt.semantic(row,probe_prefix.record(row).unwrap()).unwrap();
            assert_eq!(x,px); assert_eq!(t.state(),pt.state());
            fields.extend_from_slice(&kbytes(x));
            transcript_states.push(hex(&t.state()));
            if row >= 15 {
                let polynomial = sw::decode_values::<28>(row,original_prefix.payload(row).unwrap()).unwrap();
                let kpoly = semantic::decode::<28>(row,probe_prefix.payload(row).unwrap()).unwrap();
                for (a,b) in polynomial.into_iter().zip(kpoly) {
                    assert_eq!(a.to_le_bytes(),kbytes(b)); polynomial_values += 1;
                    fields.extend_from_slice(&a.to_le_bytes());
                }
                let boundary = aspis_core::state_only_sumcheck::r0::boundary(&polynomial);
                let value = aspis_core::state_only_sumcheck::r0::evaluate(&polynomial,x);
                for (a,b) in [running,boundary,value].into_iter().zip(new.round_checks[(row-15) as usize]) {
                    assert_eq!(a.to_le_bytes(),kbytes(b)); fields.extend_from_slice(&a.to_le_bytes());
                }
                running = value;
            }
        }
        let terminal = public.terminal(&old.claims,&old.alpha,&old.challenges).unwrap();
        assert_eq!(terminal.to_le_bytes(),kbytes(new.terminal));
        let masked = aspis_core::state_only_hiding::r0::masked_terminal(&old.claims,&old.alpha,old.challenges.eta,terminal);
        assert_eq!(masked.to_le_bytes(),kbytes(new.masked_terminal));
        fields.extend_from_slice(&terminal.to_le_bytes()); fields.extend_from_slice(&masked.to_le_bytes());
        let mut high_component_rejections = 0;
        for row in 14..27u8 {
            let offset = 32+(0..row).map(|r|5+sw::row_shape(r).unwrap().1).sum::<usize>();
            let count = sw::row_shape(row).unwrap().1 / 32;
            for value in 0..count {
                let mut bad = prefix.to_vec(); bad[offset+5+value*32+16] = 1;
                assert!(semantic_wire::Prefix::parse(&bad).is_err());
                high_component_rejections += 1;
            }
        }
        fixtures.push(json!({"fixture":name,"native_acceptance":true,"all_outputs_bitwise_equal":true,
            "round_polynomial_values":polynomial_values,"round_check_values":30,
            "semantic_challenges":25,"point_claim_values":87,"before_z1_values":29,
            "terminal_check_values":2,"high_component_mutations_rejected":high_component_rejections,
            "proof_sha256":hex(&Sha256::digest(&proof)),"proof_bytes":proof.len(),
            "public_sha256":hex(&Sha256::digest(&public_bytes)),"public_bytes":public_bytes.len(),
            "field_trace_sha256":hex(&Sha256::digest(&fields)),"field_trace_bytes":fields.len(),
            "transcript_states":transcript_states,"state_before_z0":hex(&new.state_before_z0),
            "state_after_z1":hex(&new.transcript.state())}));
    }
    let result = json!({"label":"UNPROVED R1 COST PROBE P2; semantic gate only",
        "baseline":"S4 semantic phase; retained fixture bytes, no CU rerun",
        "sampler_blocks":blocks.len(),"sampler_digest":hex(&sampler_digest.finalize()),
        "circle_checks":blocks.len()*2,"fixtures":fixtures});
    std::fs::write(out,serde_json::to_string_pretty(&result).unwrap()+"\n").unwrap();
    println!("{}",result);
}
