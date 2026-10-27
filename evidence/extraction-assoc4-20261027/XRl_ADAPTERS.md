# Adapter audit

Target not yet established. No security-top premise removed. The original
semantics below use the exact emitted callbacks plus pinned library operations;
they do not assert an unproved Rust compiler/extraction P6 theorem.

| Adapter | Checked law | Status for requested full native association |
|---|---|---|
| XRk_enumerateNext | XRl_Adapter.enumerateNext: full Result, iterator/count, and restoration callback equal explicit mutable Enumerate semantics | Local ABI law proved for fixed concrete mutable-slice operation; dictionary argument is ignored, not a generic dictionary law. Underlying library/source P6 remains. |
| XRk_intoIter | XRl_Adapter.intoIter: full Result and array restoration function equal application of emitted backward projection to restored initial state | Local ABI law proved; library/native allocation/carrier obligations retained. |
| XRk_fromFnState | XRl_Adapter.fromFnState: fail/div/ok, array and final capture equal explicit sequential fromFnList semantics | Local ABI law proved; native library/closure refinements retained. |
| XRk_revRestored | XRl_Adapter.revRestored: full Result and backward composition equal original projection applied to restored initial adapter | Local ABI law proved; does not validate next_back. |
| XRk_enumerateRestored | XRl_Adapter.enumerateRestored: analogous full Result/backward law | Local ABI law proved. |
| XRk_reverseNext | XRl_Adapter.reverseNext_not_equivalent | Universal request FALSE: resets forward cursor to zero via XRk_StdExtra.next_back. Stop this association chain. |
| Dropped next_back restoration | XRl_Adapter.next_back_projection | Value/state projection only; next_back_not_equivalent refutes native equality even before writeback. |
| Dropped next restoration | XRl_Adapter.next_projection; restoration_not_erasable | Projection proved; arbitrary mutable-borrow final-state equality FALSE. A singleton false value changed to true is restored only by the original callback. |
| closure_1 FnMut | XRl_Adapter.closure_1_FnMut, closure_1_mut_once | Full modeled Result/final capture preserved by applying returned restoration callback. Underlying reverse loop still needs restricted-domain native refinement. |
| closure_1 FnOnce | XRl_Adapter.closure_1_FnOnce_projection | Scalar projection only: fixed FnOnce ABI contains no returned capture. Full final borrowed-capture equivalence remains OPEN. |

Counterexample: slice [true], forward cursor 1. XRl_Adapter.exhausted_reachable
proves it follows one actual mutable next from cursor 0. Cursor-respecting
originalNextBackValue returns None; adaptedNextBackValue returns Some true.
The original semantics follows Rust core slice iterator next_back's empty-span
check, modeled by the pinned shared next_back with the actual cursor. This
refutes universal equivalence but does not establish that the deployed sampler
reaches this mixed forward/backward history: its fresh rev starts at cursor 0.
The restriction must be proved at each relevant caller, never silently added
to the requested every-input statement. No predecessor model is edited.

All accepted laws have #print axioms in their receipts, standard axioms only.
No passing projection is counted as full Result/state/P6 association. No new
trust item is introduced.

Additional restricted-domain evidence: XRl_ReverseDomain and XRl_ReverseCursor
prove exact full modeled reverse equality at cursor zero and cursor preservation
through next_back/restoration on matching states. XRl_ClosureCapture proves the
actual emitted mutable closure's returned restoration callback is identity.
These do not turn the false every-input reverse law into a proved one or supply
whole caller/native P6. L099 audits all accepted adapter laws together.
