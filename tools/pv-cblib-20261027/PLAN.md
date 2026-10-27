Source law route, in order of dependency:

1. Extract each shipped library method with the pinned Charon/Aeneas pair,
   recording the upstream source version/hash. Restrict impl patterns to the
   method rather than including an entire alloc impl.
2. If a caller wrapper causes Drop/loan rejection, start at the actual
   dependency method using the documented impl-first start-from syntax. This
   does not modify LLBC or erase Drop.
3. Where the method itself is unsupported, extract an owned safe reference;
   compare native shipped = reference with bounded-loop, no-stub Kani on the
   prover's actual instantiation. Keep gate bounds explicit. A missing gate
   never becomes a source-law premise.
4. Compose carrier selections, publish all successful opN_source laws through
   PV_CBL_CallbackBundle, audit each law with #print axioms, audit the complete
   bundle in the last three charged Lean attempts. Keep names stable.

Path.join/as_ref/deref are pure path/string operations. They perform no
filesystem lookup, open, stat or other OS effect. Any extraction difficulty
is a source/backend difficulty, not a reason for native-effect deferral.
