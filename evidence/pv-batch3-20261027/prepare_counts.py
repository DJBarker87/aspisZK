"""Produce an evidence-only instrumentation patch; do not apply in git source."""
from pathlib import Path
import difflib
R=Path.cwd();D=R/'evidence/pv-batch3-20261027';p=R/'crates/aspis-prover/src/host_forest.rs';s=p.read_text();t=s
names=['materialize_mask_cells','materialize_active_rows','pool_v1_pair_forest_copy_active_row_masks_v1','build_pool_v1_pair_forest_copy_registry_v1','pool_v1_pair_forest_copy_inactive_row_masks_v1']
for i,name in enumerate(names):
 a=t.index('pub fn '+name+'(');b=t.index('{',a)+1;t=t[:b]+f'\n    PV_B3_COUNTS[{i}].fetch_add(1,std::sync::atomic::Ordering::Relaxed);'+t[b:]
t+='''
pub static PV_B3_COUNTS:[std::sync::atomic::AtomicU64;5]=[const{std::sync::atomic::AtomicU64::new(0)};5];
pub fn reset_counts(){for n in &PV_B3_COUNTS{n.store(0,std::sync::atomic::Ordering::Relaxed);}}
pub fn counts()->[u64;5]{std::array::from_fn(|i|PV_B3_COUNTS[i].load(std::sync::atomic::Ordering::Relaxed))}
'''
(D/'forest-counts.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True),fromfile='a/crates/aspis-prover/src/host_forest.rs',tofile='b/crates/aspis-prover/src/host_forest.rs')))
# An exact comparator binary can use the base example; remove its whole-prover
# timing metric and record only operation counters and byte commitments.
p=R/'crates/aspis-r1-cost-probe/examples/prover_rw_gate.rs';s=p.read_text();s=s.replace('time::Instant','time::Duration')
s=s.replace('let started = Instant::now();','aspis_prover::host_forest::reset_counts();')
s=s.replace('let seconds = started.elapsed().as_secs_f64();','let counts=aspis_prover::host_forest::counts();')
s=s.replace('"seconds":seconds,','"counts_132_133_134_228_inactive134":counts,')
(D/'fixture_counts.rs').write_text(s)
