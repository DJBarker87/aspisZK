# LPg P6 continuation

Target not yet established. Budget: 30 Kani / 60 Lean, one admitted capped scope at a time. Only LPg modules and this evidence directory may change. No pushes.

Order: field-operation contracts and Dot push; echeck; check_values; validate_record_fields; expand_values; decode_k; claims; wide_view; full leaf ledger.

Reuse checked LPa/LPc models; no whole-buffer Kani loops. Contracts/invariants must be established by callers. Frozen Cargo.lock graph is checked before every offline Kani invocation, and lock hash after it. Scratch-only instrumentation is committed as patches; shipped source remains unchanged.

Baseline actual top: AspisR1.FJv_Top.deployed, owner-provided 83T/3P/13G. No premise removal is claimed at initialization. Standard axioms only. Runtime/source/ELF and SAME carrier joins remain explicit.
