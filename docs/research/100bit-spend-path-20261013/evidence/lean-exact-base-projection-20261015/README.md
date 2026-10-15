# Exact base projection focused proof

Target `R1ExactBaseProjection` was checked in the pinned NUC workspace using the retained 4G high / 6G max / 0 swap / 128 task cap. Attempt `exact-base-projection-a` failed because the simplifier did not reduce the direct prime-field-to-wide algebra map through all nested quadratic algebras. Attempt `exact-base-projection-b` uses the explicit composition of the three canonical algebra maps and succeeded.

The final module defines `embed : M31Exact →+* WideExact` and the coordinate projection `project x := x.re.re.re`. It proves the projection is a left inverse and that embedding the projection recovers exactly the values in `embed.fieldRange`. It does not state that `project` preserves ring operations on arbitrary `WideExact` elements. The three public theorem audits report `[propext, Classical.choice, Quot.sound]`.

Source revision: `57edab99fe104f23b3d3c881d1e87c1abb0975c0`. Final source SHA-256: `762d9cea59495ee9f227c2df2c0c8ec4182ea0f8f46bc714d351a2228eb31cec`. Final target object SHA-256: `a1947b0c7941a14cef560eb4e7ed8b5123308890313edd47862b3f5dca405357`.

The `attempts/` directory retains source snapshots, both compiler logs, timing logs, source sidecars, and receipts. `imports/` retains the exact imported tower sources and object hashes used by the focused workspace; `runner/` contains the exact compile wrapper, harness, and environment snapshot.
