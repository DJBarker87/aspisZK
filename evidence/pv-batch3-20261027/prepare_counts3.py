from pathlib import Path
import difflib
D=Path('evidence/pv-batch3-20261027');R=Path.cwd();patch=(D/'group2-counts.patch').read_text();p=R/'crates/aspis-r1-cost-probe/src/host_public.rs';s=p.read_text();t=s
for i,name in enumerate(['materialize_public_bytes','terminal_qm31']):
 a=t.index('pub fn '+name+'(');b=t.index('{',a)+1;t=t[:b]+f'\n    PV_B3_PUBLIC[{i}].fetch_add(1,std::sync::atomic::Ordering::Relaxed);'+t[b:]
 if i==1:
  b=t.index('{',a)+1;t=t[:b]+'''\n    let mut prefix=10usize;while prefix>0 && (alpha[prefix-1]==QM31::ZERO || alpha[prefix-1]==QM31::ONE){prefix-=1;}
    PV_B3_TERMINAL_PREFIX[prefix].fetch_add(1,std::sync::atomic::Ordering::Relaxed);
'''+t[b:]
t+='''
pub static PV_B3_PUBLIC:[std::sync::atomic::AtomicU64;2]=[const{std::sync::atomic::AtomicU64::new(0)};2];
pub static PV_B3_TERMINAL_PREFIX:[std::sync::atomic::AtomicU64;11]=[const{std::sync::atomic::AtomicU64::new(0)};11];
pub fn reset_counts(){for n in &PV_B3_PUBLIC{n.store(0,std::sync::atomic::Ordering::Relaxed);}for n in &PV_B3_TERMINAL_PREFIX{n.store(0,std::sync::atomic::Ordering::Relaxed);}}
pub fn counts()->[u64;2]{std::array::from_fn(|i|PV_B3_PUBLIC[i].load(std::sync::atomic::Ordering::Relaxed))}
pub fn prefix_counts()->[u64;11]{std::array::from_fn(|i|PV_B3_TERMINAL_PREFIX[i].load(std::sync::atomic::Ordering::Relaxed))}
'''
patch+=''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile='a/crates/aspis-r1-cost-probe/src/host_public.rs',tofile='b/crates/aspis-r1-cost-probe/src/host_public.rs'));(D/'group3-counts.patch').write_text(patch)
s=(D/'group2_fixture_counts.rs').read_text().replace('aspis_prover::host_forest::reset_counts();','aspis_prover::host_forest::reset_counts();aspis_r1_cost_probe::host_public::reset_counts();').replace('let counts=aspis_prover::host_forest::counts();','let public_counts=aspis_r1_cost_probe::host_public::counts();let terminal_prefixes=aspis_r1_cost_probe::host_public::prefix_counts();let counts=aspis_prover::host_forest::counts();').replace('"mle_prefix_counts":prefixes,','"mle_prefix_counts":prefixes,"public_counts_226_227":public_counts,"terminal_prefix_counts":terminal_prefixes,');(D/'group3_fixture_counts.rs').write_text(s)
s=(D/'group2_count_build.py').read_text().replace("mlebackup=mle.read_bytes();example=", "mlebackup=mle.read_bytes();pubsource=S/'crates/aspis-r1-cost-probe/src/host_public.rs';pubbackup=pubsource.read_bytes();example=").replace("'group2-counts.patch'","'group3-counts.patch'").replace("'group2_fixture_counts.rs'","'group3_fixture_counts.rs'").replace('mle.write_bytes(mlebackup);manifest.', 'mle.write_bytes(mlebackup);pubsource.write_bytes(pubbackup);manifest.');(D/'group3_count_build.py').write_text(s)
