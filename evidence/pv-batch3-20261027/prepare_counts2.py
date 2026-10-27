from pathlib import Path
import difflib
R=Path.cwd();D=R/'evidence/pv-batch3-20261027';p=R/'crates/aspis-prover/src/host_forest.rs';s=p.read_text();t=s
names=['materialize_mask_cells','materialize_active_rows','pool_v1_pair_forest_copy_active_row_masks_v1','build_pool_v1_pair_forest_copy_registry_v1','pool_v1_pair_forest_copy_inactive_row_masks_v1',None,'materialize_copy_helper']
for i,name in enumerate(names):
 if name is None:continue
 a=t.index('pub fn '+name+'(');b=t.index('{',a)+1;t=t[:b]+f'\n    PV_B3_COUNTS[{i}].fetch_add(1,std::sync::atomic::Ordering::Relaxed);'+t[b:]
t+='''
pub static PV_B3_COUNTS:[std::sync::atomic::AtomicU64;7]=[const{std::sync::atomic::AtomicU64::new(0)};7];
pub static PV_B3_PREFIX:[std::sync::atomic::AtomicU64;11]=[const{std::sync::atomic::AtomicU64::new(0)};11];
pub fn reset_counts(){for n in &PV_B3_COUNTS{n.store(0,std::sync::atomic::Ordering::Relaxed);}for n in &PV_B3_PREFIX{n.store(0,std::sync::atomic::Ordering::Relaxed);}}
pub fn counts()->[u64;7]{std::array::from_fn(|i|PV_B3_COUNTS[i].load(std::sync::atomic::Ordering::Relaxed))}
pub fn prefix_counts()->[u64;11]{std::array::from_fn(|i|PV_B3_PREFIX[i].load(std::sync::atomic::Ordering::Relaxed))}
'''
patch=''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile='a/crates/aspis-prover/src/host_forest.rs',tofile='b/crates/aspis-prover/src/host_forest.rs'))
p=R/'crates/aspis-r1-cost-probe/src/host_multilinear.rs';s=p.read_text();a=s.index('pub fn multilinear_evaluate_qm31(');b=s.index('{',a)+1
insert='''
    aspis_prover::host_forest::PV_B3_COUNTS[5].fetch_add(1,std::sync::atomic::Ordering::Relaxed);
    let mut prefix=10usize;while prefix>0 && (point[prefix-1]==QM31::ZERO || point[prefix-1]==QM31::ONE){prefix-=1;}
    aspis_prover::host_forest::PV_B3_PREFIX[prefix].fetch_add(1,std::sync::atomic::Ordering::Relaxed);
'''
t=s[:b]+insert+s[b:];patch+=''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile='a/crates/aspis-r1-cost-probe/src/host_multilinear.rs',tofile='b/crates/aspis-r1-cost-probe/src/host_multilinear.rs'));(D/'group2-counts.patch').write_text(patch)
s=(R/'crates/aspis-r1-cost-probe/examples/prover_rw_gate.rs').read_text().replace('time::Instant','time::Duration').replace('let started = Instant::now();','aspis_prover::host_forest::reset_counts();').replace('let seconds = started.elapsed().as_secs_f64();','let counts=aspis_prover::host_forest::counts();let prefixes=aspis_prover::host_forest::prefix_counts();').replace('"seconds":seconds,','"counts_132_133_134_228_inactive134_222_224":counts,"mle_prefix_counts":prefixes,');(D/'group2_fixture_counts.rs').write_text(s)
# Generate the invocation from the reviewed previous driver, restoring both sources.
s=(D/'fixture_count_build.py').read_text().replace("pbackup=p.read_bytes()", "pbackup=p.read_bytes()")
s=s.replace("example=S/", "mle=S/'crates/aspis-r1-cost-probe/src/host_multilinear.rs';mlebackup=mle.read_bytes();example=S/")
s=s.replace("'forest-counts.patch'", "'group2-counts.patch'").replace("'fixture_counts.rs'", "'group2_fixture_counts.rs'")
s=s.replace("p.write_bytes(backup);manifest.write_bytes(mbackup);example.unlink()", "p.write_bytes(backup);mle.write_bytes(mlebackup);manifest.write_bytes(mbackup);example.unlink()")
(D/'group2_count_build.py').write_text(s)
