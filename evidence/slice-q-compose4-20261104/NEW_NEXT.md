# Current geometry dependency order

1. Typed literal repair: same signed/unsigned count9, then exact checked-to-wrapping shift law. The complete raw geometry file now compiles (L013); the raw file is retained unchanged separately. Its std externals reuse OraclePortStdBuilder/Port3_BatchStd/Port4C_GeometryStd, with no axioms introduced.
2. Scalar/CM transports (L016) and prefix source helper (L018) are complete. NEW_GeometryPointPrimitives binds literal frozen tables and nominal CM results next. Reuse all NEA/NEB arithmetic/canonical proofs.
3. Point and line association, then native/cohort terminal callbacks, reverse buffer and full-loop Result mapping, then root association and native fidelity. No newly extracted function or std adapter is itself a composed row.
4. Only after the geometry root closes, proceed to the query root. Peer b79efe6ea6 has no additional slice row to import; check again within 30–60 minutes.

L021 is currently waiting at the admission barrier, with refusal recorded and no scope launched. No other own scope runs. No timeout or memory kill has occurred; no limit was raised.
