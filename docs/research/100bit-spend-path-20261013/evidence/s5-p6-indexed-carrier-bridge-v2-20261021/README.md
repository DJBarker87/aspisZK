# S5 P6 indexed carrier bridge, receipt-complete revision

This source-only packet supersedes the previous carrier-bridge packet because the original runner did not capture Git HEAD at process launch. The unchanged target was run once more under the shared local lock; `run-focused.py` captures HEAD after lock acquisition and active-Lean exclusion, then records the exact command and receipt.

The bridge proves that V24's exact 32-byte output under the corrected explicit P6 model agrees with V11's expected byte array through an explicit fieldwise carrier map. P6-to-Rust-Std correspondence and indexed-candidate adoption remain open.
