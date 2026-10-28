# Prepared op15 native SDK point pilot

This is an exploratory caller fragment, not a proposed complete slot closure.
The actual authentication function is invoked and validate_verifier_policy_v1
is replaced by its checked contract. A harness-only expected pointer is set to
master.verifier_policy. Its contract requires pointer identity, making the
native caller prove that property when the site is reached. Natural Result
postcondition is exact and the native policy body remains unchanged.

The pointer precondition is an ADDED harness-domain condition. It is not
established for every upstream caller and therefore is a finding under ruling
D, never a new assumption of the release theorem. Passing this pilot cannot
close op15(ii). The prepared wrong-pointer control was not run. K068 tests a Result
assertion not implied by the contract/context. K059/K066 invalidate both
postcondition controls by also failing the callee ghost precondition; no native
bridge credit is assigned to this pilot. The local full typed policy
proof/control and local contract-use pair must pass first.

The pilot fixes the policy's gate bindings to their frozen constants and
requires the immutable-registry bit. Registry metadata is writable, forcing
rejection before any PDA/SHA path. The account fixture aliases three arguments
and is outside the enclosing parent's unique-account accepted class. This is
intentional diagnostic scope, not upstream coverage. No SHA is unwound, no
PDA or account-borrow implementation is replaced, and no success/closed-caller
or accepted-execution extraction component may be inferred.

Full op25–34 authentication association remains blocked on a controlled route
through the intervening registry/entry decode and PDA calls on ONE accepted
native execution. No unverified PDA, decoder, allocator or borrow stub is
permitted to bypass those dependencies. Lean projections already supplied by
NBX are not re-proved as a substitute for that native component.

Observed: statement contract K058 PASS; initial consumer K060 cannot compile
without Arbitrary for the real return enum. A cfg-only implementation enumerates
all eight actual variants; repaired consumer K061 passes and K062 fails its
assertion. Program K063 cannot compile the KMX registration without cfg-only
alloc linkage; K064 then rejects dependency-only proof_for_contract registration.
Program-local proof K065 passes; K066 fails TWO properties (postcondition and
callee precondition), so it is not a valid matched control. Actual unchanged
authentication K067 passes 3143 checks (240 unreachable); K068 fails the intended
Result assertion. These are PROVISIONAL diagnostic results, not native closure.

The ghost precondition is not established by every upstream caller, and the
fixture forces a rejection suffix using aliased account arguments. Both are
findings; no accepted-execution/general-domain extraction component is proved.
The next concrete fix is to align each inverse wrapper's explicit domain with
the callee and set the expected pointer in its harness. Prepared unexecuted
patch NCF_policy_control_fix.patch needs a new authorized Kani budget.
