# Root statements and hypothesis inventory

Target not yet established. Native-contract semantic transport remains explicit P6/D188 option-A trust reclassification. These are hybrid packets, not kernel theorems parsed directly from Rust.

```lean
theorem NJP_PermutationPacket.TX1_306 : ∀ (input : State) (states : Fin 23 → State)
  (control : Fin 22 → ℕ × NJA_Trace.Kind),
  NJP_ControllerTrace.Cut input states control →
    states (Fin.last 22) = model input ∧
      ok ((), states (Fin.last 22)) = ok ((), model input) ∧
        ∀ (r : Fin 22),
          ((NJE_RoundTrace.observed input states r).round, (NJE_RoundTrace.observed input states r).kind) = control r
```

```lean
theorem NJP_CompressionPacket.TX1_305 : ∀ (left right : Digest),
  (∀ (i : Fin 8), ↑(left i) < 2147483647) →
    (∀ (i : Fin 8), ↑(right i) < 2147483647) →
      ∀ (seeded : State) (out : Digest) (calls : ℕ),
        CallerCut left right seeded (NJP_PermutationPacket.model seeded) out calls →
          out = model left right ∧ calls = 1 ∧ ok out = ok (model left right)
```

TX1:306 inputs are the original complete raw state, 23-stage raw state chain and typed descriptor sequence. The only logical input is the reviewed parent Cut: it expands to the K006/K007 fixed controller descriptor plus witnessed leading/round cell/layer native stage cuts with child replies substituted at the SAME arguments. NJE_RoundTrace.one/facts discharge arithmetic/canonicality and every 22-stage next-state domain; NJP_FieldEncoding.unique recovers the complete raw state from the field result. There is no arbitrary operation dictionary, free successful-child result or model endpoint hypothesis. Native child/stage cut provenance is separately pinned in NJP_REUSED_PINS.json; the association is the explicitly retained hybrid tool trust. The deployed callback is the no-op instance, with K008/K009 rename stability.

TX1:305 inputs are both original raw eight-limb digests, their own canonicality clauses, the logged sixteen-limb seeded state, returned digest and call count. The only other hypothesis is the reviewed arbitrary-reply CallerCut instantiated with the permutation model at that very seed. The canonical seed/callee domain is proved by child_domain, not assumed. The output/copy association is established by K057 PASS and K058/K059 semantic FAIL under both explicit slice-copy and ptr-copy KMX annotations; the unchanged Lean root and gate1 are reused. No parent acceptance, different permutation seed, reselected root, free dictionary, successful-child equation or new trust row appears.


## Final root admission

The two root statements above were replayed with the deployed headline in L078 and raw-audited in L080. Their aq(2) hypothesis inventories remain in NJP_ROW_PACKETS.json. TX1:127 and TX2:093 have no accepted final root statement; NJP_VerifierView is uncompiled and is excluded. Neither shared loop/returning theorem is substituted for either requested root or an endpoint/caller-domain hypothesis. See NJP_REMAINING.md for the independent missing obligations.
