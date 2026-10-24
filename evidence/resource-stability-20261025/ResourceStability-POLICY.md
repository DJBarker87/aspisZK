# Reviewed policy statements and source noninterference

This packet changes an OFFLINE operator-policy predicate. It establishes no
physical memory/reclaim/future property and no Lean/native/security theorem.
The policy has not been adopted. The public live entrypoint raises unconditionally.

Let V(s) mean the complete unchanged ResourceAvailable scanner/observe checks
and visibility evidence appropriate to s; P(s) is the explicit ordered
ResourceStability structural projection; C(s) is the explicit collector binding.
Let L be unchanged legacy visibility/nonreserve/frontier binding, F the phase
rules, I the unchanged inside-scope binding, and N the checked numerical policy.
These are actual source predicates, not a structure carrying output equality.

Before (pure Available):
  allowed iff L ∧ F ∧ (inside ⇒ I(before)=I(after))
    ∧ membership(before)=membership(after) ∧ V(before) ∧ V(after) ∧ N.
Before ResourceAdmit additionally requires exact preregistered scope unit for
inside-scope and propagates collection failures to DENY. Prospective pure
Available did not require explicit self evidence.
After (ResourceStability20261025-v1):
  allowed iff L ∧ F ∧ V(before) ∧ V(after)
    ∧ C(before)=C(after), both C present in validated membership
    ∧ P(before)=P(after)
    ∧ (inside ⇒ unchanged I(before)=I(after) and explicit expected unit match)
    ∧ N.
Outside synthetic/offline inputs there is no callable live admission implementation;
missing self evidence denies even synthetic inputs. No provenance follows from
caller-supplied snapshots. Original capture failures are retained separately and
are never replaced by a counterfactual decision.

Exact projection, in row order:
path,parent,root,enabled,owner,subtree_memory,type,domain,procs_errno,
controllers,pids_enabled,subtree_pids,tasks_max,populated,cap,high,swap_max.
Conditional absence of memory fields is unchanged scanner semantics, represented
by None as in the old membership projection; populated is absent only at root.
All old structural/control equality fields remain, with root added explicitly.
Raw cgroup.subtree_control and every raw scanner field remain unchanged in
captures; scanner's existing memory/pids delegation model is reused, not enlarged.

Only unrelated procs/threads/identities leave the cross-snapshot equality gate.
pids.current was never in the old equality projection; its exact per-subtree
count remains checked independently in each snapshot. It is not pids.max and
cannot be frozen across legitimate births/exits. All five original v2 count
deltas are retained. Neither changed counts nor terminated tasks create credit.
Internally missing, changed, unreadable, malformed, duplicate or vanished
identities are not excused: unchanged scan rechecks stat/starttime, status,
unified membership and complete proc/thread consistency and errors deny.

Retained assumptions: complete visible hierarchy and per-snapshot identity/
receipt validation; full finite frontier and controls; raw checked numerical
inputs; phase/legacy gates; inside-scope effective ancestors, self and count-once
binding. Changed premise: unrelated cross-snapshot identity equality is removed.
Added policy premise: prospective explicit self equality/presence. Inside-scope
unit expectation is explicit, preserving the original Admit supplement. No
new trust assumption. No cryptographic or native premise is discharged. No
blanket stronger-domain conclusion: the prospective self obligation is stronger.

## Source-level noninterference argument

For two complete internally valid snapshot pairs, hold each phase's raw numeric
inputs and ordered P fixed, and hold C fixed and validated. Allow only unrelated
membership/identity values and their consistently updated pids.current counts
to vary. This hypothesis is raw-field equality and internal validity, not
numerical-result equality.

1. In observe, frontier selection uses row order, enabled, populated, finite cap,
   path and ancestry. Those are in P. Thus the same complete finite frontier is
   selected and B=sum(full caps) is unchanged. No PID-derived term enters B.
2. Top memory-owner selection uses enabled/owner/root path. R=MemTotal-MemFree
   -sum(top current) is unchanged. Neither task movement nor exit rewrites R.
3. M,A,K,S are global numerical inputs. T=K-floor(S/2), and pair min M, max A,
   max T and max R are unchanged. All checked additions/subtractions retain the
   same results or failures. Hence adjustedAvailable is unchanged.
4. With Q and L fixed, B+Q, B+Q+7GiB and strict comparisons to 55GiB,
   adjustedAvailable, and min M>Q+2GiB are unchanged. The entire evaluator
   numerical/legacy suffix is AST-identical to the pinned Available source,
   verified in focused tests and the source audit. Membership-derived outputs
   root_direct_pids and disabled_coverage.procs are diagnostics only; no equal
   full-output claim is made. Validation is essential and is not relaxed.

Primary Linux semantics motivate this distinction: hierarchical memory.max is
not a per-listed-process sum; memory ownership/charges do not disappear merely
because task membership changes. This is a policy/data-dependency inference
using reused primary-source assessments, not a new kernel identity check or
proof that independently read quantities bound physical usage at another time.
A stable populated frontier is still required; no missing row/current is replaced.
The non-atomicity, kernel estimate and over-limit limitations remain intact.
