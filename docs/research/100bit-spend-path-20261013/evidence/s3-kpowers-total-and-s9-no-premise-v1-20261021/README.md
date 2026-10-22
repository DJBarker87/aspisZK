# Constructive `kpowers` totality for the retained S9 join

This packet adds a constructive success theorem for the selected P6 `weights.kpowers` model: canonical seed implies the model array succeeds. It composes that result into the previously checked S9 scalar-factor theorem, eliminating the free `hpowers` premise for the same `p`, seed, and output witness.

The `hmap` relation tying the input power-array `p` to the retained `weights.powers` trace remains explicit. The P6 model's correspondence to Rust `core::array::from_fn`, and the enclosing Rust caller assignment to `ap0`, remain open. This is not a full S9 or frozen-caller refinement.

Both focused checks exited 0 under Lean 4.32, `-j1 -M4400`; peak RSS values and standard-only axiom lists are retained per module. Exact launch argv/source revision were not retained by the scratch runner and are explicitly not inferred. The dependent scratch object was hashed from the retained `/tmp` object; no OLean is included.
