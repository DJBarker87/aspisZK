# Checked producer stage

41200–41220 consumed, including uncharged preflight41216 (no host scope:
missing PV_CB_ProducerTuple dependency).20 charged Lean attempts so far.
Receipt source snapshots preserve every failed source. No caps were raised.
A dependent preflight was issued before its failed predecessor had been
repaired; it launched no compiler. Subsequent dependent stages follow green
predecessors. This ordering mistake provides no proof evidence.

Accepted final targets:
- ProducerPost41200, ProducerBind41201: generic Result postconditions;
- ProducerCell41202: actual copy_cell preserves canonical words when input
  reads and offset are canonical, with installed release scalar primitives;
- ProducerRead41203: successful actual slice/array/vector read membership;
- ProducerTry41207: exact core Try/from_residual composition;
- ProducerLimb41208: actual copy_tuple_limb, both banks and zero branch;
- ProducerMake16 41210: symbolic finite16 array construction;
- ProducerTuple41217: actual full copy_tuple_values success invariant;
- ProducerContext41218: source congruence on exactly op55 and op73;
- ProducerSelected41219: transfer to PV_CurrentScaleInstall.selected;
- Op223CanonicalDomain41220: tag+selected sampler+canonical array reference.

All accepted declarations have standard axioms only, zero swap, and their
exact source/dependency hashes, target, status, wall, peak RSS, revision and
#print axioms in the numbered receipts. This is not a full release replay.

The16-value numerical invariant is now proved through the actual producer,
under explicit canonical-trace-read and canonical-offset input invariants.
Those input conditions have not yet been connected to the complete shipped
builder/registry. No desired compressor output is assumed. Rejections and
divergence remain in the exact Result. No op223 source binding or row closure
is claimed; V164 hypotheses are unchanged. Target not yet established.
