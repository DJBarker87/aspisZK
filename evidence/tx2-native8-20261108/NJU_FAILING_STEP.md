# NJU failed attempts

NJU_L004: inspection used four incorrect fully qualified names. Corrected own inspection input; no theorem failed and no native credit claimed.

NJU_K001: cargo compilation stopped on missing frozen tools/r1-builder-reference/tree.rs, referenced by aspis-statement cfg(kani). Added exact Git 4bb3b3f source to own committed scratch input payload. This changes the failed input and preserves dependency validation. No verifier was run, timeout or memory kill occurred.

NJU_K002: compilation stopped on a second missing cfg(kani) tool, records.rs. Imported all retained NJR tools/ inputs into the committed payload, preserving their frozen bytes. No proof verdict.

NJU_K003: own harness module used a nested-module default path. Added explicit path attribute; only cfg(kani) attachment changes. No verification or timeout.

NJU_K004: exact KMX generic allocator stubs require cfg(kani) allocator_api in the scratch crate root, as in NJR. Added that cfg-only feature attribute; no shipped source edit.

NJU_K009/K011 should_panic verdicts are existential diagnostics only. They are not universal arbitrary-input abort certificates. K013/K015 retain every raw property: only the expected panic fails and the explicit post-return false assertion succeeds; canonical controls K014/K016 fail that exact continuation assertion. No safety check was disabled. Full caller composition remains unproved.

Lean work-in-progress failures L010/L011 (namespace and namespace-shadowing repairs), L012 (small True conjunction repair), L019/L025 (scalar proof shapes), L015/L017/L020/L021/L024/L026/L029/L030 (logged monad erasure and tactic repairs) are not selected proof evidence. Source changes precede every retry; no cap or timeout change.
