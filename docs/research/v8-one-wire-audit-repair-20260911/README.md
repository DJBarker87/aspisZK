# V8 one-wire audit repair

Isolated audit/repair of `research/v8-no-work-100-20260907` at
`30a303a344dbb42e24ad8f42a8804819747942bc`.

Reproduce the supplied representation diagnostic:

```sh
python3 results/v8-one-wire-audit-repair-20260911/audit_checks.py
```

It is Python only, not Lean, Rust, SBF or a payment test. See `report.md` for
the exact checked scope and open boundaries.
