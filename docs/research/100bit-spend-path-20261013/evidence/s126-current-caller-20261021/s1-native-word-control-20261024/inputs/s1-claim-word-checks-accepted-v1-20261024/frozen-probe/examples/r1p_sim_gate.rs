//! G-sim gate (LOG D44.3; optimized build only): the explicit simulator simE
//! from the public statement alone, timed per step, and each simulated proof
//! verified (strict tx1+tx2 and dense) under its programmed oracle. Seeds come
//! from the OS; nothing from the simulated transcripts is recorded.
use aspis_r1_cost_probe::sim;
use serde_json::json;
use std::path::Path;

fn main() {
    assert!(!cfg!(debug_assertions), "run this gate with an optimized profile");
    let args: Vec<_> = std::env::args().collect();
    assert_eq!(args.len(), 3, "usage: r1p_sim_gate <runs> <out.json>");
    let runs: usize = args[1].parse().unwrap();
    let out = Path::new(&args[2]);
    assert!(!out.exists(), "refusing to overwrite {}", out.display());
    let fixture = aspis_prover::r0_fixture::prepare(false);
    let public = fixture.public();
    let mut rows = vec![];
    for i in 0..runs {
        let mut seed = [0u8; 32];
        getrandom::fill(&mut seed).expect("OS entropy");
        let t = std::time::Instant::now();
        let s = sim::sim_e(public, seed).expect("simulated view");
        let wall = t.elapsed().as_secs_f64();
        let v = std::time::Instant::now();
        let (ok, programmed, read) = sim::verify_programmed(public, &s.proof, s.table.clone());
        let verify_seconds = v.elapsed().as_secs_f64();
        let public_bytes=public.public_bytes().unwrap();
        let real_strict_rejected=aspis_r1_cost_probe::verifier::tx1(public,&public_bytes,&s.proof,
            aspis_r1_cost_probe::verifier::SPLIT,aspis_core::digest::LegacyHashFn(aspis_prover::HOST_HASH),None).is_err();
        let real_dense_rejected=aspis_r1_cost_probe::dense::verify(public,&s.proof,aspis_prover::HOST_HASH).is_err();
        let tm = s.times;
        rows.push(json!({"run": i, "attempts": s.attempts, "wall_seconds": wall,
            "draw_seconds": tm.draw, "p_r1_seconds": tm.p_r1, "tape_seconds": tm.tape,
            "semantic_seconds": tm.semantic, "opening_seconds": tm.opening, "program_and_serialise_seconds": tm.program,
            "simulation_without_p_r1_seconds": wall - tm.p_r1,
            "real_hash_strict_rejected":real_strict_rejected,"real_hash_dense_rejected":real_dense_rejected,
            "proof_bytes": s.proof.len(), "transcript_reads": s.transcript_reads, "commitment_reads": s.commitment_reads,
            "programmed_addresses": programmed, "programmed_addresses_read_by_verifier": read,
            "verified_strict_and_dense_under_programmed_oracle": ok.is_ok(), "verify_seconds": verify_seconds}));
        println!("R1SIM_RUN {i} attempts={} wall={wall:.3} p_r1={:.3} semantic={:.3} opening={:.3} program={:.3} verified={} programmed={programmed} read={read}",
            s.attempts, tm.p_r1, tm.semantic, tm.opening, tm.program, ok.is_ok());
        assert!(real_strict_rejected && real_dense_rejected,"real hash must reject");
        assert_eq!(programmed,read,"all programmed addresses must be read");
        assert_eq!(programmed,s.transcript_reads+s.commitment_reads);
        assert_eq!(s.proof.len(),aspis_r1_cost_probe::compact::PROOF_BYTES);
        assert!(ok.is_ok(), "simulated proof must verify under its programmed oracle");
    }
    let report = json!({
        "label": "UNPROVED R1 cost probe: G-sim, explicit simulator simE (R0Z/RefPayload) in the ideal game fsR1.ideal (R1Z/GamesR1)",
        "variant": "S2 (R1)", "statement": "transfer fixture public statement (r0_fixture::prepare(false)); no compiled trace or witness is passed to simE",
        "seed_source": "OS entropy, one 32-byte seed per run", "runs": rows,
    });
    std::fs::write(out, serde_json::to_vec_pretty(&report).unwrap()).unwrap();
}
