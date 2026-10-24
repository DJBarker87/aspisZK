"""Summarize retained receipts without replay; preserve every source/flag pin."""
from pathlib import Path
import hashlib,json,re,subprocess
D=Path(__file__).resolve().parent
R=D.parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/native-owned-drop'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for p in sorted((E/'packet').glob('*/receipt.json')):
 j=json.loads(p.read_text());log=(p.parent/'stdout.log').read_text();before=json.loads((p.parent/'admission-before.json').read_text());go=json.loads((p.parent/'admission-barrier.json').read_text())
 assert before['allowed'] and go['allowed']
 assert j['swaps']==0 and j['peak_rss_kib'] is not None
 row=dict(receipt=str(p.relative_to(E)),receipt_sha256=sha(p),**j)
 row['admission_before_sha256']=sha(p.parent/'admission-before.json');row['admission_barrier_sha256']=sha(p.parent/'admission-barrier.json')
 row['reserved_before_bytes']=before['bounded_reserved_bytes'];row['reserved_barrier_bytes']=go['bounded_reserved_bytes']
 if j['kind']=='kani':
  assert j['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in log
  row['verification_result']=re.search(r'\*\*.*',log)[0]
 if j['kind']=='extraction' and j['target'].startswith('aeneas'):
  assert j['exit_status']==2 and j['drop_flags']['effective_drop_as_no_op'] is False
 rows.append(row)
parent=E.parent/'native-drop-abi/ledger.json'
source_paths=['crates/aspis-prover/src/state_only_entropy.rs','crates/aspis-r1-cost-probe/src/RealR1_client.rs','crates/aspis-r1-cost-probe/src/prover.rs','Cargo.lock','Cargo.toml','crates/aspis-prover/Cargo.toml','AGENTS.md','design/PROVER-RW-20261024-NATIVE-OWNED-DROP.md']
assessment=dict(source_revision_label=(D/'revision.txt').read_text().strip(),source_identity='Per-file hashes identify proof inputs. Design revision label does not assert a new native source/binary identity gate.',current_repository_source_sha256={p:sha(R/p) for p in source_paths},scope='No shipped source changes. Actual zeroize1.8.1 default feature dependency compiled; getrandom0.3.4/OS source not verified here.',new_validation='Kani045-050; Charon045/047; rejected Aeneas046/048. Scoped read-only audits001/002. No Lean/native reference/release gates.',reused='Prior private candidate014 binary and Config/Main hashes plus failed Guard and selected69 inventory are reused with exact hashes; not revalidated as an accepted backend or new identity gate.',missing_preflight_binary_pins='Charon executable and cargo/time/timeout shims were not hashed in extraction preflights; postrun-artifacts.json supplies explicitly POST-RUN hashes. Aeneas and Kani verifier/compiler binaries were hashed preflight and rechecked at go. This limitation is not retroactively an identity gate.',metadata='tool-versions.txt rustc is host default, not a claim about Kani frontend rustc; Kani package/compiler hashes and dependency .d records identify that frontend. audit001/002 expected_phase generic extraction text is inaccurate: both commands were only read-only postrun hash/source inspections. audit002 adds missing Charon/shim hashes; no proof was replayed.',premises_before_after='Identical existing native/refinement/E1 theorem statements. No premise added, removed, weakened, or moved into a structure. No whole-output equality premise.',memory_scope='See REPORT: stronger049/050 use fresh root post-drop pointer; initial047/048 child-pointer observations are Kani-model-only. Compiler fence sequential, Rust aliasing/provenance argument source-inspected, not mechanized.')
(E/'source-assessment.json').write_text(json.dumps(assessment,indent=2)+'\n')
ledger=dict(schema='ProverRwOwnedDrop-ledger-v1',parent_ledger_sha256=sha(parent),backend_used=15,backend_ceiling=16,backend_remaining=1,extraction_used=48,extraction_ceiling=48,extraction_remaining=0,lean_used=236,lean_ceiling=260,lean_remaining=24,kani_used=50,kani_ceiling=60,kani_remaining=10,kani_this_step=6,kani_step_ceiling=8,kani_step_remaining=2,optimized_rust_test_check_commands=0,optimized_rust_test_check_ceiling=4,charon_release_commands=2,rows=rows,claim='Universal actual pinned array Zeroize32/64 and exactly-once retained-storage Zeroizing Drop32/64 physical zero/frame relation under Kani. No emitted helper or owner/event/error/unwind integration theorem.',print_axioms='N/A for every new result: no Lean declaration/emission, no new axiom or theorem. Existing statements unchanged.',next_producer='Use these exact Kani/P6 leaf relations to bind an actual supported emitted caller/glue interface, preserving normal errors and unwind separately. Concrete-only monomorphized extraction remains untested; extra extraction allocation is exhausted.',targets='Both deployed targets not yet established; E1/OS/16-inner/8-outer/native owner-event/L1-L2-L3/adoption remain open and unchanged.')
(E/'ledger.json').write_text(json.dumps(ledger,indent=2)+'\n')
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=5_000_000,p
print(json.dumps({k:v for k,v in ledger.items() if k.endswith('_used') or k.endswith('_remaining')}))
