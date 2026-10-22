#!/usr/bin/env python3
"""Record unchanged before/after; refuse to report a premise weakening."""
import subprocess,hashlib,json
from pathlib import Path
E=Path(__file__).resolve().parent.parent
P='docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployed.lean'
before=subprocess.check_output(['git','show','47ccfa22c:'+P]);after=Path(P).read_bytes()
assert before==after
for label,data in [('before',before),('after',after)]:
 (E/('endpoint-'+label+'.lean.txt')).write_bytes(data)
(E/'endpoint.diff').write_text('')
(E/'endpoint-status.json').write_text(json.dumps(dict(source=P,base='47ccfa22c',before_sha256=hashlib.sha256(before).hexdigest(),after_sha256=hashlib.sha256(after).hexdigest(),changed=False,premises_removed=[],premises_added=[],remaining=['RustProverRefinement, real WholeRunJoin and ideal WholeRunJoin'],new_deployed_endpoint=False,claim='No deletion or strict weakening achieved; shipped-prover target not yet established.'),indent=2)+'\n')
text=before.decode();start=text.index('def RustProverRefinement : Prop :=');end=text.index(' := by',text.index('theorem privacy_headline_deployed',start))
statement=text[start:end]
r=Path('docs/research/v8-r0-zk-20261009/r1p-final/PROVER-COMMIT17-20261021.md')
s=r.read_text();assert '## Verbatim endpoint before' not in s
s+='''
## Stage 4 — whole-run obstruction and retained endpoint

`ProverCommitRuntimeObstruction17.no_unrestricted_endpoint` constructs an
independently supplied experiment with inhabited singleton randomness
carriers, identical disclosed views, and a public oracle-history-length bit
that differs between real and ideal runs. Its distinguishing advantage is
exactly one. Therefore deleting the refinement premise while leaving the
existing `rust : FSExperiments` quantification unrestricted is false for
any epsilon below one. This is a countermodel to that proposed inference,
**not an attack on the shipped prover**, and not a proof that a concrete
shipped adapter cannot be verified.

J8643 initially misses the explicit Fintype instances for the defined
carriers. Changed J8644 passes the countermodel's axiom audit with only
`[propext, Classical.choice, Quot.sound]`: exit 0, wall 1.58s, peak RSS
3489488 KiB, swaps 0, revision `9cb63237e` plus exact source snapshot hash.
All host caps and launcher slot locks are unchanged.

**Target not yet established.** No new deployed endpoint or strict weakening
is claimed. No premise is removed, added, repackaged, or renamed in the
existing endpoint. The before/after source is byte-identical; `endpoint.diff`
is deliberately empty and `endpoint-status.json` records both hashes.
Neither a whole-run real coupling nor a whole-run ideal coupling has been
constructed. The countermodel means local helper checks cannot justify an
unrestricted premise deletion; it does not turn unfinished concrete runtime
work into a proved impossibility.

Remaining concrete deliverables are:

1. Instantiate an independent shipped experiment from its exact input/entropy
   carriers, builder/checker/retry behavior, visible errors, ordered proof
   bytes, and retained shared-oracle history. The existing endpoint has no
   such concrete instance. No concurrent-worker module was touched to obtain
   one by assumption.
2. Supply arbitrary-length borrowed-Vec/source iteration identification and
   transport the new owned extraction to the old material/model types.
   Verify the full semantic framing, source sort/dedup and multiproof traversal,
   rather than promoting the emission-cell checks to those claims.
3. Establish exact retained transcript recovery on success and abort, then
   instantiate both existing WholeRunJoin obligations (real and ideal), with
   the fixed bad events and the same randomness law. OS entropy, nonce-store
   reservation, allocation/disposal and sampler/model alignment remain explicit
   implementation boundaries, not new cryptographic assumptions.

The next narrow source deliverable is a complete serializer source model,
including its semantic-row and multiproof-node iterators, with arbitrary
prefix Vec semantics and Rust-to-List transport. The new cell checks and
all-length induction can be reused there. A model alias named “shipped”
would not supply either missing WholeRunJoin and is not introduced.

## Verbatim endpoint before

The following exact declaration span includes the refinement definition and
full theorem signature; its unchanged surrounding local notations and types
are in `endpoint-before.lean.txt`.

```lean
'''+statement+'''
```

## Verbatim endpoint after

No new endpoint is substituted. The exact same declaration span remains:

```lean
'''+statement+'''
```
'''
r.write_text(s)
