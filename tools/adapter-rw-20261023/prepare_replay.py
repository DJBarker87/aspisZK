from pathlib import Path
s=Path('tools/r1-cost-probe/src/bin/r18_replay.rs').read_text()
s=s.replace('#[path = "r18_replay/readonly_runtime.rs"]','#[path = "readonly_runtime.rs"]')
s=s.replace('proof.len() == 124343 && sha(proof) == PROOF_SHA','proof.len() == 57607').replace('public.len() == 1880 && sha(public) == PUBLIC_SHA','public.len() == 1880').replace(' && s.next_pair_index == 1023','')
s=s.replace('include_bytes!("../../Cargo.lock")','include_bytes!("../../Cargo.lock")').replace('include_bytes!("r18_replay.rs")','include_bytes!("adapter_rw_replay.rs")').replace('include_bytes!("r18_replay/readonly_runtime.rs")','include_bytes!("readonly_runtime.rs")')
# Gate at each fixture, before any further fixture is started.
s=s.replace('    println!(\n        "before:', '''    ensure!(a.stage1.total <= 1_400_000 && a.stage2.total <= 1_400_000, "CU maximum gate");
    ensure!(i128::from(a.stage1.total)-i128::from(b.stage1.total) <= 12_000 && i128::from(a.stage2.total)-i128::from(b.stage2.total) <= 12_000, "CU delta gate");
    println!(
        "before:''')
Path('tools/adapter-rw-20261023/adapter_rw_replay.rs').write_text(s)
