# Port22ARENA handoff

Branch `codex/cx-port22arena-20261024`, base `51ff811857`. No merge/push,
production source change, key operation, trust extension or release claim.

Established:
- Exact copied solana-program-entrypoint2.3.0 BumpAllocator body passes one
  native Kani harness: 0/84 failures,1unreachable. It checks returned pointer/
  null, actual cursor update, success interval/alignment4/8 and arbitrary
  selected noncursor-word preservation in a256-byte admitted native arena.
  All nonzero valid request sizes are symbolic; null is not conditioned away.
  This is Kani-model evidence, not a deployed SBF or native Vec proof.
- `Port22ARENA_Bump` proves source-matched mask/alignment/saturation/range,
  exact normal cursor-store/null branch and outside-byte frame. Modeled cuts
  retain prior history; actual abort/oracle interpretation remains open.
- `Port22ARENA_WordBody.candidate_word` connects literal64-bit wrapping/
  saturating arithmetic to that candidate under no-overflow/positive-align.
- `Port22ARENA_VecFrame.fresh_reserve_length/empty` derives zero length and
  empty initialized range from disjoint cursor/ptr/cap stores at every modeled
  prefix. Native Vec field/store association is explicit and unproved.

Retained assumptions and missing native producer are spelled out, with full
before/after statements, in NATIVE-OBLIGATION.md. No desired whole-helper result
is hidden in a primitive record. D157 excludes unsafe/allocation failure;
D189 is the approved SDK snapshot/private account projection. Neither nor
P2/P6/P7 supplies general Vec content/no-oracle semantics. Source audit records
full QM31 clone, actual [u64;4] TrivialClone specialization and map_err; their
native resize/pointer/field composition remains open. Both targets not yet
established; privacy cleanup and all-outcome ordered query accounting remain.

New validation:6Lean attempts (4green,2retained elaboration failures), one native
Kani check, one focused statements/axioms import audit (21 standard-only
reports). Peak Lean RSS677920768bytes, swap0. Native0.868326s,
peak aggregate RSS116383744bytes, cgroup peak216363008bytes, swap0;
1536MiB/2GiB/swap0/Tasks64. Fresh full hierarchy admission twice before launch,
26.172456960GB populated reservations plus2GiB, conservative uncapped RSS and
7GiB OS reserve; no unknown live process omission. Exact commands, hashes,
revisions, wall/RSS/swap/axioms and failed originals are in manifest/receipts.
Final core/job dependency audit hashes850modules/5091files at go.

Reused:Port21 exact-source graphs/emission, warm Lean core; relevant bytes and
tools rehashed. No old source evidence is relabelled as a new identity gate.
Budget:6/13Lean,1/1Kani,0/2extraction,0/2standalone optimized Rust;
backend/full-manifest/ELF0. Accounting baselines326/368Lean and4/20Kani
exclude concurrent lead allocations;7job Lean remain,35unassigned unchanged.
Next: selected native shim/RawVec fresh-field interpretation described above,
then actual resize/full Clone/map_err composition. No broad allocator
certification or new trust is requested.

## Stage history

b9b77d581c Link exact word arithmetic and record native source assessment
1fd3097c5a Derive zero-length frame from disjoint source stores
1f536dbfe9 Record native allocator frame and specify length-field bridge
9cbc562322 Restrict allocator check to valid calls and retain resource gates
6370d4e9bf Prove allocator arithmetic and freeze native arena check
1df824c8b0 Specify selected allocator primitive and native boundary
