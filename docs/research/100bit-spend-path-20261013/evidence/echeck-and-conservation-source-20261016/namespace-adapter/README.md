# Echeck source namespace split (source only; not compiled)

This split is derived from the frozen echeck attempt-a Aeneas output. `Types.lean` and `Funs.lean` retain the entire generated declaration set, including the exact `verifier.echeck_loop`, `verifier.echeck`, and `verifier.echeck_round1` bodies. The only changes in those files are the module import path and outer Lean namespace (`AspisR1SelectedMaskProbe` → `AspisR1EcheckCut`) needed to keep this probe’s WideExact/field carriers distinct from the selected-mask extraction.

`FunsExternal.lean` retains the generated standard-library source annotation for `core.option.Option.ok_or`, but replaces the opaque template axiom with a typed definition delegating to the already checked prefix-aggregate Aeneas model. This is the sole external template. It is an explicit reused Lean model, not a body extracted by this echeck run. It carries the pinned Rust `core/src/option.rs` `Option::ok_or` implementation. No other generated declaration is removed or stubbed.

Run `./generate_split.py` to regenerate from the pinned local output. The script checks input SHA-256 values before producing output and records hashes in `manifest.json`. No Cargo, Charon, Aeneas, Lean, or source production build was run for this split.
