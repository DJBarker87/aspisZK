# R519 arithmetic bridge inventory

Read-only inventory against selection
`R519SharedGammaPartsSelection.llbc`, SHA-256
`e614a35673713638504c4c4e83387dbee819805a510094aff7bc76b45826e606`.
The selected root is `Fun107`,
`aspis_v8_performance_host::r17_host_relation::shared_gamma::parts`.
Its retained source text has one CM31 `add` followed by three M31 `add` calls.

| R519 LLBC call | exact retained declaration | available prior bridge |
| --- | --- | --- |
| `Fun107`, structured statement 6 → `Fun94` | `aspis_core::field::{CM31}::add`, source `field.rs:233:4–233:39`; structured | No R159/R251 direct CM31-add theorem identified in this inventory. `FunsCore.lean` defines it at lines 709–718 as two M31 additions. |
| `Fun107`, structured statements 19, 36, 53 → `Fun175` | `aspis_core::field::{M31}::add`, source `field.rs:56:4–56:37`; structured | `AspisV8R19.R159WideBaseExecution.add_success` and `add_encode` directly name `field.M31.add`; `double_encode` is its self-add specialization. |

`R159WideBaseExecution.lean` SHA-256:
`be997bd5e28d0a6eacbec3947d30a26270213e898f10035a25a95ce441e58035`.
Relevant exact declarations:

```lean
theorem add_success (x y : U32) (hx : x.val < P) (hy : y.val < P) :
  ∃ z : U32, field.M31.add x y = .ok z ∧
    z.val = (x.val+y.val)%P ∧ z.val < P

theorem add_encode (x y : M31Exact) :
  field.M31.add (encodeBase x) (encodeBase y) = .ok (encodeBase (x+y))
```

`R251PrivateAddSub.lean` SHA-256:
`09a45a0aea0c904604ef07c40c6e1b470ed4cdbe9b5122dbd479c5a614e2f353`.
Its named addition results are `b_add_canonical` and `b_add_encode`; both
name `B.add` from the private R110 scalar context, rather than `field.M31.add`.
They are recorded as available prior arithmetic results, but the current R519
M31 calls above do not syntactically name `B.add`.

This is declaration and call routing only. No translation, compilation,
source-execution correspondence, or theorem-premise decision was made.
