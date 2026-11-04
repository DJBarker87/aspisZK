# Incoming checkpoint domain review

SOURCE REVIEW ONLY; no new theorem or native result. Input revisions and hashes are in NGC_INPUT_PINS.json. No NFW proof imported or credited. The inspected NFW branch tip has powers as its only newly CLOSED function, not Prepared::new/prepare. Its missing NFW_HANDOFF.md / NFW_REMAINING.md are recorded as unavailable, not inferred results.

The existing KNE_Caller.WriterDomain p a requires exactly:

- p.variant = S2;
- a.weights.val.length = 64;
- every index in the SAME p.queries array (all 22) is <262144;
- CanonicalFields (fields p a size queriesBound);
- a.next.val = 10.

KNE_Caller.DriverEstablishedDomain additionally quantifies over reached calls and requires witnesses pm, am for SAME S1S7S8StateProvenance p a pm am. KNE_Caller.every_reached_call CONSUMES this premise. It does not discharge it. No accepted-run hypothesis is introduced here.

NFS_QueryLoopRoot.tx1 establishes equality of a ten-fuel loop and the cohort query_loop on its input Domain and a.next=0. It does not, in that theorem's conclusion, export WriterDomain for the returned accumulator. NFS_QueryInvariant.Domain contains weights length/canonicality, rhs canonicality, power/rho canonicality, pending Progress, offset and upper bound. Its step theorem preserves that invariant at successful child steps. To derive a.next=10, prove the loop's successful terminal is stopped, combine next>=10 with upper<=10, and propagate the invariant through that SAME run. Equality of loop functions alone is insufficient.

NGC-B1: the actual checkpoint prestate is AFTER candidate.rs:287 pending.finish(&mut a.weights), not the accumulator returned at :286. Need the BatchedWeights::finish result/frame law on this SAME pending/weights pair: weights length stays64, every written K limb is <2147483647, rhs/power/next unchanged, and values correspond to the same pending residue rows. A native/model/domain bridge for this call is outside the job's enumerated function list (D SCC206); request/cite its CLOSED packet rather than silently treating query_loop's output as checkpoint's input. The exact model predicate needed is WriterDomain p { a_loop with weights := finish_weights pending a_loop.weights }, plus SAME provenance transport. No claim is made that the existing Progress definition cannot imply the mathematical bounds; the source-to-model bridge and explicit implication still need checking.

NGC-B2: NFS's invariant does not contain p.variant=S2, all22 query bounds, gamma/kappa/alpha[0..1]/semantic_alpha/z/claim canonicality or preparation provenance. NFS_PacketRoot.Domain contains alpha0/alpha1 but these remain caller inputs. Derive these facts from the SAME accepted prepare/Prepared::new outputs and their actual samplers/claims/semantic provenance. NFW_PreparedFields.source is an output projection theorem, not a proof that the supplied fields meet these predicates. Never pick independent canonical fields or a different prepared witness.

CM31 byte writer's native valid-buffer domain can be len(out)>=8 with arbitrary raw u32 limbs; QM31 can use len(out)>=16. Canonicality is needed for the eventual checkpoint semantic encoding, not for these raw stores. Both writers preserve the suffix beyond their written prefix. Native tests must also describe or explicitly exclude short-slice panic domains justified by every caller. KNE packet domains must be retargeted to canonical RPz7 owners before composition next to RPx; its legacy import graph has not been replayed here.
