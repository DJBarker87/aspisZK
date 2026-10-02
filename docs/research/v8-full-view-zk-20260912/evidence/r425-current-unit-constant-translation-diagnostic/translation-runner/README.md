# R425 translation runner — prepared only

This runner is adapted from the reviewed R424 translation runner. It keeps the unchanged R419 candidate LLBC (SHA256 `7f82eaabe855e89d735b21f9af5f6a983abea6b2f4d93d4b8bae747abd2829e2`), R396 baseline LLBC, root selector and command flags. It assigns a fresh R425 output directory, systemd unit, and Lean namespace.

The R425 executable path and hash deliberately remain unresolved. `--launch` is fail-closed until the main compiler build has succeeded, the executable path/hash are fixed, and a separate lead approval file is provided. This draft has not been launched; it performs no translation. It makes no claim about generated output, Lean axioms, or source correspondence.
