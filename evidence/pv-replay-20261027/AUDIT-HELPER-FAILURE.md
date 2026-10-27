# Diagnostic failure retained: 28176

The complete project closure remains successful (537 reused / 135 compiled). The first diagnostic adds no theorem, but Lean rejected its tuple-pattern lambda/loop syntax. Exact errors and complete output: receipts/out-28176.log and receipt-28176.json. All three explicit endpoint prints nevertheless succeeded with exactly [propext, Classical.choice, Quot.sound]. This is not an exhaustive audit result.

PV_ReplayAudit.lean and its failed receipt are retained unchanged. PV_ReplayAudit2.lean is a separate diagnostic using explicit pair projections and a concrete Name × Name annotation. It changes no existing project proof or statement. A new attempt is charged for this changed helper, never an unchanged retry. The full audit is still pending.
