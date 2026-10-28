# NCI local substitutions

| Stub | Named Lean theorem | Domain and caller evidence |
|---|---|---|
| `NCI_value::reduce` replacing `aspis_core::field::M31::reduce_u64` | `AspisR1.NCI_PendingReducer.reducer_ok` (L014); `primitive_eq` identifies selected S8 emitted primitive | Every U64; returns ok with exactly x mod2147483647 and canonical output. Local value/one-iteration finish pass the SAME row limbs directly. No nonlinear assume, no multiplication replacement. |
| `core::ptr::copy_nonoverlapping` / byte `copy_from_slice` | Exact KMX patch; inherited `KMX_CopyMeaning.loop_spec`, `copy_frame`, `append_spec` value laws, plus `AspisR1.NCI_WindowFrame.cell/after` (L010) | Width1/4/16/32 reader windows, scalar/codec windows and native getter/Vec windows. Each credited gate needs its own matched failing control in the same configuration. Full native1768 ownership/lifetime projection is OPEN. |

KMX patch SHA256 `bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67`, copied verbatim within NCI_reader.patch. No own copy stub. No field multiplication is executed or proved in Kani. Digest Request is a concrete generic backend supplied to the actual resume; it checks request slices and returns the selected reply. It is not a SHA implementation or a SolanaDigest realization. The latter is the named U00 lower bridge/runtime trust boundary.

The planned Reader contract fidelity controls use wrappers on the exact64-byte window class. A64-byte precondition is stronger than the parent1768-byte resume establishes: that is an explicit open domain finding; such a contract may compose local windows only, never directly replace the parent read. No contract credit before all required per-shape controls pass.

| Opaque multiplication call log | Paired emitted theorem | Domain |
|---|---|---|
| `NCI_steps::mul` replacing `M31::mul`; records lhs/rhs/reply and allows any canonical reply, with no nonlinear assume | `AspisR1.NCI_FieldLog.instantiate` (L020), `Realized`; uses `AspisR1.LPf_BaseMultiply.source` for the exact emitted ok/product-mod-P reply | Native step establishes canonical actual inputs and unchanged exact operands in the log. The native window is parametric in every canonical reply; Lean selects the concrete emitted reply in that class. Native gate itself does not prove multiplication or assert that an arbitrary log is realized. |

Native node double/sub execute their real bodies. Enclosing native/cohort credit retains the named U01 `DoubleSubBridge` on canonical intermediate operands; this lane does not claim to close that lower unit. Source-cut statements are byte-matched to the frozen function body in NCI_STEP_SOURCE.json; they are single statements on arbitrary pre-state, not whole Rust parent executions.
