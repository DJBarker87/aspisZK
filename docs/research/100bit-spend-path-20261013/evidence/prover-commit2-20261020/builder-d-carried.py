from pathlib import Path
p=Path('/home/dombarker/project-offloads/codex-cx-prover-commit2-20261020/source-builder/crates/aspis-prover/src/state_only_entropy.rs')
s=p.read_text()
a='        let mut d = SensitiveQm31Vec(Vec::with_capacity(STATE_ONLY_POSEIDON_TRACE_ROWS));\n        for _ in 0..STATE_ONLY_POSEIDON_TRACE_ROWS {\n            d.0.push(expander.qm31()?);\n        }'
b='        let mut result = Ok(SensitiveQm31Vec(Vec::with_capacity(STATE_ONLY_POSEIDON_TRACE_ROWS)));\n        for _ in 0..STATE_ONLY_POSEIDON_TRACE_ROWS {\n            result = match result {\n                Ok(values) => append_profile21_d_cell(&mut expander, values),\n                Err(error) => Err(error),\n            };\n        }\n        let mut d = result?;'
start=s.index("    fn derive_pool_v1_zero_factor_d(")
index=s.index(a,start)
s=s[:index]+b+s[index+len(a):]
p.write_text(s+'\nfn append_profile21_d_cell(expander: &mut Profile21SourceExpander, mut values: SensitiveQm31Vec) -> Result<SensitiveQm31Vec, StateOnlyMaskBuildError> {\n    let value = expander.qm31()?;\n    values.0.push(value);\n    Ok(values)\n}\n')
