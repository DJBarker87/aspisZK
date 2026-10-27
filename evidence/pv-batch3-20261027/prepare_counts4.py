from pathlib import Path
import difflib
D=Path('evidence/pv-batch3-20261027');R=Path.cwd();patch=(D/'group3-counts.patch').read_text();p=R/'crates/aspis-prover/src/host_arithmetic.rs';s=p.read_text();t=s
for i,name in enumerate(['state_only_selected_mask_value','evaluate_state_only_polynomial']):
 a=t.index('pub fn '+name+'(');b=t.index('{',a)+1;t=t[:b]+f'\n    PV_B3_ARITHMETIC[{i}].fetch_add(1,std::sync::atomic::Ordering::Relaxed);'+t[b:]
 if i==0:
  b=t.index('{',a)+1;t=t[:b]+'''\n    let mut prefix=10usize;while prefix>0 && (point[prefix-1]==QM31::ZERO || point[prefix-1]==QM31::ONE){prefix-=1;}
    PV_B3_MASK_PREFIX[prefix].fetch_add(1,std::sync::atomic::Ordering::Relaxed);
'''+t[b:]
t+='''
pub static PV_B3_ARITHMETIC:[std::sync::atomic::AtomicU64;2]=[const{std::sync::atomic::AtomicU64::new(0)};2];
pub static PV_B3_MASK_PREFIX:[std::sync::atomic::AtomicU64;11]=[const{std::sync::atomic::AtomicU64::new(0)};11];
pub fn reset_counts(){for n in &PV_B3_ARITHMETIC{n.store(0,std::sync::atomic::Ordering::Relaxed);}for n in &PV_B3_MASK_PREFIX{n.store(0,std::sync::atomic::Ordering::Relaxed);}}
pub fn counts()->[u64;2]{std::array::from_fn(|i|PV_B3_ARITHMETIC[i].load(std::sync::atomic::Ordering::Relaxed))}
pub fn prefix_counts()->[u64;11]{std::array::from_fn(|i|PV_B3_MASK_PREFIX[i].load(std::sync::atomic::Ordering::Relaxed))}
'''
patch+=''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile='a/crates/aspis-prover/src/host_arithmetic.rs',tofile='b/crates/aspis-prover/src/host_arithmetic.rs'));(D/'group4-counts.patch').write_text(patch)
s=(D/'group3_fixture_counts.rs').read_text().replace('aspis_prover::host_forest::reset_counts();','aspis_prover::host_arithmetic::reset_counts();aspis_prover::host_forest::reset_counts();').replace('let counts=aspis_prover::host_forest::counts();','let arithmetic_counts=aspis_prover::host_arithmetic::counts();let mask_prefixes=aspis_prover::host_arithmetic::prefix_counts();let counts=aspis_prover::host_forest::counts();').replace('"terminal_prefix_counts":terminal_prefixes,','"terminal_prefix_counts":terminal_prefixes,"arithmetic_counts_117_121":arithmetic_counts,"mask_prefix_counts":mask_prefixes,');(D/'group4_fixture_counts.rs').write_text(s)
s=(D/'group3_count_build.py').read_text().replace('pubbackup=pubsource.read_bytes();example=',"pubbackup=pubsource.read_bytes();arithmetic=S/'crates/aspis-prover/src/host_arithmetic.rs';abackup=arithmetic.read_bytes();example=").replace("'group3-counts.patch'","'group4-counts.patch'").replace("'group3_fixture_counts.rs'","'group4_fixture_counts.rs'").replace('pubsource.write_bytes(pubbackup);manifest.','pubsource.write_bytes(pubbackup);arithmetic.write_bytes(abackup);manifest.');(D/'group4_count_build.py').write_text(s)
