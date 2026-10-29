from pathlib import Path
import json,subprocess,hashlib
D=Path(__file__).parent;s=json.loads((D/'summary.json').read_text());rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();rows=[]
for r in s['sources']:
 path=Path(r['path']).resolve().relative_to(Path.cwd()).as_posix();raw=subprocess.check_output(['git','show',rev+':'+path]);assert hashlib.sha256(raw).hexdigest()==r['sha256'];rows.append(dict(**r,repository_path=path,git_blob=subprocess.check_output(['git','rev-parse',rev+':'+path],text=True).strip()))
(D/'final-source-identity.json').write_text(json.dumps(dict(source_revision=rev,rows=rows,all_compiled_source_bytes_match=True,note='Launch revision labels are baselines; dirty inputs are pinned by each source snapshot and hash. Final sources resolve byte-for-byte at this exact commit.'),indent=2)+'\n')
cleanup=json.loads((D/'cleanup.json').read_text())['removed'];links=sum(r['symlink'] for r in cleanup)
p=D/'REPORT.md'
with p.open('a') as f:
 f.write(f'''
## Verification, failures and stop condition

**100/100 Lean attempts**, IDs 65000–65099; **5/40 capped native scopes**, **0 Kani**. 95 Lean attempts pass. Each launch has allowed:true AND admission exit0 in the same wrapper. No refusal, cooldown slip, VOID run or overlapping scope occurred. All scopes use MemoryHigh6G,MemoryMax8G,MemorySwapMax0,TasksMax64; Lean -M7000. Total GNU-time wall **{s['total_gnu_wall_seconds']}s**, maximum peak RSS **{s['peak_rss_kib']:,}KiB**, all swaps **0**. `attempts.json` and raw receipts retain every target/command, source and dependency hash, revision label, exit, wall, RSS, swaps and printed axioms.

| Audit | Exact target | Exit | GNU wall | Peak RSS KiB | Swap | Launch revision label |
|---|---|---:|---:|---:|---:|---|
''')
 for n in [65097,65098,65099]:
  r=json.loads((D/f'lean{n}-receipt.json').read_text());f.write(f"| {n} | `{r['module']}` | {r['exit']} | {r['gnu_wall']} | {r['peak_rss_kib']} | {r['swaps']} | `{r['source_revision']}` |\n")
 f.write(f'''
65097 audits all **73 new theorems**, including the final disclosed/oracle pair and complete-decision equalities at the actual deployed interface. 65098 audits V2 and the deployed roots. All final axiom sets are subsets of {{propext, Classical.choice, Quot.sound}}. 65099 is the **single final diagnostic-job manifest replay**, not a full privacy-release replay. `final-pre.json` checks 1,016 objects; `final-post.json` checks **1,019 objects with zero source/object/dependency mismatches**. The reused sampler sources explicitly match diag4's recovered h7 generation chain. No same-source cache was reused across a changed dependency fingerprint.

The launch revision labels are baseline labels, NOT claims that dirty inputs existed at those commits. Actual inputs are pinned by their raw snapshots/hashes. `final-source-identity.json` resolves every final new module byte-for-byte to committed source revision **`{rev}`**, with git blobs and accepted compile IDs. No proved source is changed by the final report/evidence commit. A local documentation reconciliation initially passed an absolute path to git show and was corrected to repository-relative paths; no source, compiler or host action was involved.

Failed/uncredited: 65022 (insufficient unfolding in the bound), 65053 (missing explicit Except result type), 65055 (Lean indentation), 65091 (reserved identifier prefix), 65096 (missing GamesR1 namespace for R1Adv). Each replacement changed its source/proof input. 65096's two additional observer lemmas were corrected and freshly checked in audit65097. Endpoint itself is restored exactly to accepted65095 source/object; final-pre verifies this. No failed source or sorryAx object is consumed.

The smallest changed file was compiled first; new laws were added incrementally and consumers compiled after dependencies' final accepted forms. The full import-only job manifest ran once. No unchanged full regression or release rebuild was launched. No crates/programs, existing proof, simulator, observer, soundness cone or trust-list definition was edited. All evidence files are below20MB. No binary, object or archive is committed. Nothing was pushed or merged.

`cleanup.json` records removal of **{len(cleanup)-links} private compiled artifacts/executable** and **{links} private links** only. All shared cache targets, source, receipts and keys are retained. No wallet, key or nonce-state operation was performed.

**Before/after:** the stale EJR obstruction is resolved. No premise of `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` or its native/deployment refinement is removed, added, weakened or reclassified as trust. Local capture slice safety is proved under its stated constructor association; whole native joint diagnostics and full observer recovery remain P. V038,V178/V181,V336–V339,V347–V351 and V370 remain named. Existing V229,V230,V256,V257 credit is not withdrawn or re-adjudicated. T remains exactly entropy_law,entropy_kernel,observation.

Stop condition: the fresh **100-attempt Lean budget is exhausted**. The unused native ceiling does not justify redundant finite checks or replace a missing universal source law. **Target not yet established.**

Next concrete deliverable: prove complete native clone/push/unwind/resolve/formatter/CWD-drop operations, including every failure and emitting divergent prefix; instantiate nativeDiagnosticLaw/nativeTerminalLaw on the original L1 coupling; feed the named execution/events/terminal pieces into the existing PV_RJ4IDB decoder after source/cohort integration; establish disclosed/observerOracle recovery and V036–V038. The whole honest diagnostic distribution is not established by the conditional composition lemmas.

## Commits

`git log --oneline b02602fa23..HEAD` before this final report/evidence commit:

```
''')
 log=subprocess.check_output(['git','log','--oneline','b02602fa23..HEAD'],text=True);f.write(log);f.write('```\n\nThe final report/evidence commit is the branch tip; it changes no proved source.\n');(D/'COMMITS.txt').write_text(log)
