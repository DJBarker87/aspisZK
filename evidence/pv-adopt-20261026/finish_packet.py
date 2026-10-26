#!/usr/bin/env python3
"""Write proposed commands, owner decisions and the final packet sections; no execution."""
import json,pathlib
P=pathlib.Path(__file__).resolve().parent
load=lambda n:json.loads((P/n).read_text())
rows={r['id']:r for r in load('recount2-rows.json')};c=load('closure.json');support=load('support-closure.json')
items=[
('V344','Absolute timing / Docker-cap barrier','D199 recommends shrinking Docker caps to their real profile; alternatives are excluding Docker from projection or accepting the ceiling. D209/D212 hold timing to strict quiet admission; D216 passes the absolute timing gate.','Keep the quiet-window method: D216 supplies EVIDENCED (<15 s), not a universal cost law. Docker-cap changes affect scheduling only and need host-owner action.','Keep present caps/ceiling: D216 still supplies the completed gate. No permission to bypass reservation or repeat the passed gate unchanged.'),
('V345','Relative timing / Docker-cap barrier','Same D199 scheduling recommendation; D216 passes <=1.10x research in a valid quiet window.','D216 ratios 0.353/0.350 supply EVIDENCED. Choosing a Docker remedy authorizes scheduling, not privacy closure.','Retain ceiling and existing D216 evidence; no unresolved timing comparison is manufactured from recount-2 historical OPEN status.'),
('V370','Pinned compiler-preservation trust','D197 records partial disassembly/platform evidence; D216 still requires the L3 receipt. No distinct accept/reject recommendation for V370 is recorded in D197–D216. Retained D162 trust boundary is the relevant policy, not an inferred owner acceptance.','Accept explicitly for the final pinned compiler/flags/platform: V370 becomes named retained external trust; artifact association, complete audit and V371/V373/V374 remain.','Decline the trust boundary: V370 stays OPEN; require an accepted compiler-preservation proof or a newly approved platform/toolchain route. A measurement cannot discharge this trust law.'),
('V371','DOITM / CPU latency','D197 recommends enabling DOITM on the pinned host before L3 measurement, recording the mode as a platform pin, and accepting V371 only in that mode. DOITM was supported but disabled.','Authorize enablement and accept the mode-scoped latency trust: repin mode and collect the final L3 receipt. The decision alone neither changes the machine nor proves all callers constant time.','Leave mode disabled: V371 remains substantive explicit trust/open decision; branchless disassembly alone does not close it. Any alternative contract needs explicit owner approval.'),
('V373','Disassembly / inversion-domain call sites','D197 recommends L2 prove every witness-bearing try_inv operand nonzero outside already charged bad events; escalate a reachable witness-dependent zero as a protocol leak. D200 proves only the LogUp NoPole fragment.','Approve the nonzero/outside-fixed-bad policy: enumerate native reached calls/slots and audit all call sites before V373 can close. L1 pole-verdict retry branch remains modelled; the recommendation is not a nonzero proof.','If a witness-dependent zero is reached, retain the obstruction and decide a protocol/implementation repair; do not waive it, weaken the observer or silently charge a new bad event. V373 remains OPEN.'),
('V374','Quiet L3 dudect measurement','D197 records zero samples and a collector waiting for quiet. D199 recommends cap reduction; D209–D216 enforce quiet windows for prover timing. No completed L3 dudect verdict is supplied by D216.','Authorize an appropriate quiet slot and final pinned mode/binary: run the preregistered L3 collector and retain setup/statistics/receipt. A successful test gives measurement evidence only.','Keep current admission ceiling/wait for a valid quiet slot: V374 stays OPEN until qualified L3 collection. D216 fixture medians cannot substitute for leakage testing.'),
('V396','Client bundle / signer / storage / publication pin','D216 records the D196 proof-account route as merged; D209 retains the client obligation. Exact recorded recommendation to pin client-pins.json is D196 (outside D197–D216); no contrary or new bundle recommendation is recorded inside the requested interval.','Owner pins/adopts the exact signer, storage, retained-key mapping and caller/upload bundle, then supplies the actual publication/lifecycle receipt. V396 can become EVIDENCED for that scope; universal V045/V167/E1/E2 remain.','Decline or select a different bundle: retain V396 OPEN, rebind and exercise the chosen route; existing selected64 fixtures/source pins do not authorize publishing or deleting keys.'),
('V380-inversion','All reached inversions / zero boundary','D197 recommendation as V373; D200 LogUp non-pole theorem is partial. Recount 2 keeps the alias distinct from V380 TrustedStd.btree_entry_or_insert_with.','Approve fixed-bad/nonzero handling: enumerate every M31/QM31/WideExact/circle/interpolation/certificate reached slot, prove native correspondence and SAME-coupling simulation. Only completion of these proofs closes the whole row.','Reachable witness-dependent zero requires owner protocol/implementation decision and retained counterexample. No finding of such a zero is asserted by current partial evidence; row remains OPEN.'),
('V400','OS entropy failure repair A / B','D206 recommends B; D215 repeats recommendation B and says neither repair is adopted. The failure/model disagreement theorem is conditional, not a concrete outside-bad native attack.','A: accept named OsAvailable (every in-capacity draw succeeds), retain the original conclusion and eight fields. This adds an explicit deployment trust/availability condition; does not prove E1/E2 or native association.','B (recommended): give BOTH experiments the same public failure signal, including common finite signal law. This changes the model statement with owner approval; bind actual faults/decoder and prove the common law before claiming closure. Reject both: V400 stays OPEN.')]
owner=[dict(id=i,title=t,exact_recount2_row=rows[i],lead_recorded_recommendation=rec,first_ruling_consequence=a,alternative_ruling_consequence=b) for i,t,rec,a,b in items]
(P/'owner-decisions.json').write_text(json.dumps(owner,indent=2)+'\n')
# Inert Lean audit proposal. The actual final integrated root must also be imported/printed.
audit='\n'.join('import '+m for m in support['roots'])+'''\nimport Lean
open Lean Elab Command
#print axioms R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed
#print axioms ProverRwFull.ExternalFuns
#print axioms R1Z.ProverRwP6BodyData.refinement_of_data
-- Proposed support-root audit only until final concrete endpoint is installed.
run_cmd do
  let env ← getEnv
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let owner := env.header.moduleNames[idx]!
      let text := owner.toString
      if text.startsWith "R1Z.PDict_" || text.startsWith "R1Z.ProverRw" ||
          text.startsWith "R1Z.PV_" || text == "R1Z.PrivacyR1HeadlineDeployedReal" then
        logInfo m!"OWNER|{owner}|{n}"
        elabCommand (← `(command| #print axioms $(mkIdent n)))
'''
(P/'PV_Adopt_FinalAudit.lean.txt').write_text(audit)
(P/'replay-modules.json').write_text(json.dumps(dict(status='PROPOSED_NOT_EXECUTED_NOT_FINAL_RELEASE_CLOSURE',env='J',requested_id_range=[28000,29999],ids_reserved=False,lean_memory_mb=7000,memory_high_bytes=6*2**30,memory_max_bytes=8*2**30,memory_swap_max_bytes=0,tasks_max=64,headline_modules=c['topological_modules'],support_roots=support['roots'],support_modules=[m['module'] for m in support['modules']],final_audit_module='R1Z.PV_Adopt_FinalAudit',regenerate_after_concrete_endpoint_join=True),indent=2)+'\n')
commands='''# PROPOSED command list, NOT EXECUTED. Host owner/lead first reserves env-J
# 28000-29999 and prepares ONE pinned accepted integration tree + matching env-J
# cache. Do not execute this against the candidate-first multi-revision support
# inventory. Final native endpoint import/application must exist first.
# Host paths below are the established J paths; evidence lives in private R.
set -euo pipefail
T=/home/dombarker/project-offloads/aspis-fs-generic-20261006
H=/home/dombarker/project-offloads/r1-privacy-build-integration-20261019
J=/home/dombarker/project-offloads/aspis-joint-20261019
R=/home/dombarker/project-offloads/pv-adopt-final-20261026
# Before this list: freeze final-replay.tsv from the FINAL endpoint's transitive
# import DAG, dependency first, including the installed source/instance roots.
# Columns: attempt<TAB>module/path<TAB>source_sha256<TAB>deps_fingerprint.
# IDs must be the unused reserved env-J range; the final row is the final audit.
# Materialize its hashed sources to J/sources only after snapshotting old shared
# source/object files; pin external dependency objects + env/J.json + run2.py.
# Do not cold-build mathlib/Aeneas; mismatch is a preflight STOP for the lead.
# final-source-revision.txt and final-source-files.sha256 bind ONE integration SHA.
cd "$R"
sha256sum -c final-source-files.sha256
sha256sum -c external-object-pins.sha256
sha256sum -c env-and-runner-pins.sha256
# Use the current lead-managed, quiet-window-aware reservation scanner; the
# older native-entropy barrier.py asserts 5G/7G/64 and MUST NOT be used/patched.
# This path must be verified by the lead against the active shared launcher.
RESERVATION="$R/approved-reservation.py"
python3 "$RESERVATION" "$R/admission-before.json" --requested-bytes 8589934592 > "$R/admission-before.log" 2>&1
# If refused: retain ID/receipt, wait 180s, NEXT unused reserved ID, <=10 retries;
# QUIET WINDOW HOLD follows ruling (e). No scope starts until allowed=true.
# R/approved-reservation.py is a pinned copy of the lead's existing active
# scanner, NOT new infrastructure to be implemented or a bypass of admission.
systemd-run --user --scope --unit=pv-adopt-final-replay-20261026 \\
  -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \\
  /usr/bin/time -v -o "$R/scope-time.log" bash -s -- "$T" "$H" "$J" "$R" <<'SCOPE'
set -euo pipefail
T=$1 H=$2 J=$3 R=$4
cg="/sys/fs/cgroup$(sed -n 's/^0:://p' /proc/self/cgroup)"
cp "$cg/memory.high" "$R/memory.high.before"
cp "$cg/memory.max" "$R/memory.max.before"
cp "$cg/memory.swap.max" "$R/memory.swap.max.before"
test "$(cat "$cg/memory.high")" = 6442450944
test "$(cat "$cg/memory.max")" = 8589934592
test "$(cat "$cg/memory.swap.max")" = 0
python3 "$R/approved-reservation.py" "$R/admission-inside.json" --requested-bytes 0 > "$R/admission-inside.log" 2>&1
while IFS=$'\\t' read -r attempt module source_sha deps_fingerprint; do
  test "$attempt" -ge 28000 && test "$attempt" -le 29999
  test ! -e "$R/out-$attempt.log"
  test "$(sha256sum "$J/sources/$module.lean" | cut -d' ' -f1)" = "$source_sha"
  mkdir -p "$J/objects/$(dirname "$module")"
  printf '%s\\n' "$module $source_sha $deps_fingerprint" > "$R/input-$attempt.txt"
  # One module per Lean invocation; no nested systemd scope or launcher.
  # deps_fingerprint must have been validated against actual predecessor outputs.
  set +e
  /usr/bin/time -v -o "$R/time-$attempt.log" \\
    python3 "$T/evidence/run2.py" "$H/env/J.json" "$J/objects" \\
      "$J/sources" "$J/objects/$module.olean" "$J/sources/$module.lean" 7000 \\
      > "$R/out-$attempt.log" 2>&1
  status=$?
  set -e
  printf '%s\\n' "$status" > "$R/exit-$attempt.txt"
  test "$status" = 0 || exit "$status"
done < "$R/final-replay.tsv"
for metric in memory.peak memory.swap.peak memory.events pids.peak pids.events; do
  test ! -f "$cg/$metric" || cp "$cg/$metric" "$R/$metric.final"
done
SCOPE
# Preserve the exact standard-only #print axioms lines from the final audit log.
# Parse/reject every nonstandard dependency (including Formatter or sorryAx),
# require a report for the concrete adopted endpoint AND its instance, and bind
# every receipt to final-source-revision.txt. No release claim from exit 0 alone.
'''
(P/'final-replay-commands.sh.txt').write_text(commands)
# Exact per-module command templates instantiated from the support list.
(P/'support-command-list.json').write_text(json.dumps([dict(attempt=28000+i,module=x['module'],command=['python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py','/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json','/home/dombarker/project-offloads/aspis-joint-20261019/objects','/home/dombarker/project-offloads/aspis-joint-20261019/sources','/home/dombarker/project-offloads/aspis-joint-20261019/objects/'+x['module'].replace('.','/')+'.olean','/home/dombarker/project-offloads/aspis-joint-20261019/sources/'+x['module'].replace('.','/')+'.lean','7000'],source_revision=x['revision'],source_sha256=x['sha256'],status='proposed-support-only; regenerate from final integration') for i,x in enumerate(support['modules'])],indent=2)+'\n')
path=P.parents[1]/'design/PV-ADOPT-20261026.md';s=path.read_text()
def section(title,body,next_title):
 global s
 start=s.index('## '+title);end=s.index('## '+next_title,start)
 s=s[:start]+'## '+title+'\n\n'+body.strip()+'\n\n'+s[end:]
section('Final replay plan — proposed, not executed',f'''The exact proposed shell command list is [final-replay-commands.sh.txt](../evidence/pv-adopt-20261026/final-replay-commands.sh.txt); [support-command-list.json](../evidence/pv-adopt-20261026/support-command-list.json) instantiates each per-module argv. The source-audit input is inert [PV_Adopt_FinalAudit.lean.txt](../evidence/pv-adopt-20261026/PV_Adopt_FinalAudit.lean.txt); it has not been compiled. [replay-modules.json](../evidence/pv-adopt-20261026/replay-modules.json) records caps, order and ID proposal.

Reserve **env-J 28000–29999**, exclusively, through the lead before any future launch; **not reserved or used here**. The accepted global 20000–29999 range is not an allocation. No range extension or launcher edit is authorized. The proposed single scope is:

```sh
systemd-run --user --scope --unit=pv-adopt-final-replay-20261026 \\
  -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \\
  /usr/bin/time -v -o "$R/scope-time.log" bash -s -- "$T" "$H" "$J" "$R"
```

Inside it, for each dependency-first row, use the existing env-J `run2.py` (which invokes Lean `-j1 -M7000 -DElab.async=false`), one module per invocation:

```sh
/usr/bin/time -v -o "$R/time-$attempt.log" \\
  python3 "$T/evidence/run2.py" "$H/env/J.json" "$J/objects" \\
  "$J/sources" "$J/objects/$module.olean" "$J/sources/$module.lean" 7000 \\
  > "$R/out-$attempt.log" 2>&1
```

The current headline-only order is **{len(c['topological_modules'])}** repository modules from §3. The proposed **support audit** has **{len(support['roots'])} roots / {len(support['modules'])} resolved modules**, including the 24 CB source modules, four CB3 Source modules, PDict installs, conditional RunJoin endpoints and PV_Src consumers. Full roots, edges, source paths/hashes/revisions and the external-object boundary are in [support-closure.json](../evidence/pv-adopt-20261026/support-closure.json). That inventory is a **candidate-first source union for planning**, not a checked merged tree, and does not assert that these independent roots are consumed by the headline. The final coherent release module list cannot honestly be frozen before the concrete native instance and owner-selected OS-failure statement exist. At that point regenerate the DAG from **one accepted integration revision**, include the concrete endpoint/instance as roots, replace the support union with its actual transitive closure, and append the final audit exactly once. Missing external extraction objects need their own pinned source mapping from env J; do not silently treat a repository-external import as proved by this script.

Preflight before that one final replay: all changed generic lemmas and exceptional generated chunks green; generator checks where applicable; no large unfolding/norm_num/decide regressions; source and dependency fingerprints matching; safe aggregate reservation below the host limit; quiet-window marker respected; snapshots of any shared source/object overwritten. Reuse the pinned external/compiler/mathlib/Aeneas cache. **Do not use the old native-entropy barrier script**: its committed assertions are 5G/7G/64, incompatible with 6G/8G. The recipe explicitly requires the lead's existing active quiet-aware scanner (pinned into the replay evidence); this job does not repair or implement launch infrastructure. The standing shared run-joint.sh TasksMax128 is accepted only when using that launcher; this single custom scope uses64 and never nests launcher scopes.

For reservation/quiet refusals, retain receipts, wait180s, retry with the next unused ID (up to10); continue compile-free work meanwhile. Transient vanished-cgroup failures use the documented30s retry. A memory kill or timeout requires isolation/source change, never a larger cap or unchanged rerun. Stop and review at ten minutes without a new compiled target. Collect per-target exit, wall, peak RSS, swaps, source revision/hash, dependencies and full axiom lines, plus aggregate cgroup memory/swap peaks/events. Pin the compiler, environment, scanner and runner themselves.

The audit prints the headline, ExternalFuns, P6 data bridge and all imported PV_/PDict_/ProverRw declarations using the existing dict11 enumeration pattern, then must print the final installed endpoint and concrete instance. Accept only subsets of {{propext, Classical.choice, Quot.sound}}; reject Formatter/sorryAx dependencies, and inventory **named hypotheses** separately because standard axioms do not mean assumptions were discharged. A deliberate diagnostic print of the backend Formatter axiom (as in the old dictionary audit) is not a theorem dependency or a permitted exception to the final standard-only result.

Estimate: rw17's receipt `evidence/pv-rw-step-20261026/local/23809-receipt.json` reports212 theorem checks plus headline, exit0,24.06s,3,185,344,512 peak-RSS bytes,0swap, standard axioms. It is explicitly a **local cached focused audit**, not a dependency replay or a capped Linux result. D217 rounds this to24.1s/3.2GiB. Budget about1–3minutes for a warm final print pass and roughly20–120minutes for the much larger serial source closure, with wide uncertainty for extracted modules; these are planning estimates, not measurements or authorization for an unchanged regression. No cold dependency build, security gate, ELF rebuild, Kani or Rust command is part of this packet's execution.
''','Owner escalation table')
body='''The nine rows below are exactly recount-2 bucket(c), with full original row objects and consequences in [owner-decisions.json](../evidence/pv-adopt-20261026/owner-decisions.json). “Accept” is a policy/trust decision, not proof of a native law. V344/V345 are historically OPEN in recount2 but **superseded by D216 passing evidence**; V374 remains a distinct leakage measurement. Recommendations absent from D197–D216 are marked rather than invented.

| Exact ledger row | Lead's recorded recommendation | First ruling / what closes | Alternative / what remains |
|---|---|---|---|
'''
for x in owner:body+=f"| **{x['id']}** {x['title']} | {x['lead_recorded_recommendation']} | {x['first_ruling_consequence']} | {x['alternative_ruling_consequence']} |\n"
body+='''
No ruling here authorizes changes to CPU mode, Docker caps, protocol/model, release pins, bundle signing/publication, or key cleanup. Both OS repairs remain unadopted; neither is silently inserted as a hypothesis. V380-inversion never replaces V380's collection-law row. The extra D219 corpus-retention decision is outside these nine recount-2 rows and is not treated as permission to delete evidence.
'''
section('Owner escalation table',body,'Validation and premise accounting')
path.write_text(s)
