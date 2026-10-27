086 failed before elaboration: missing
codex-cx-import-union-20261022/objects/AspisR1CircleSampleWrapper/Funs.olean.
Read-only ls confirms this exact retained leaf exists in the already-selected
codex-cx-prover-commit22-20261021/r4-cache. The FIy093/our086 LEAN_PATH orders
are identical, but the earlier partial namespace root now prevents leaf lookup.
Move the SAME existing r4-cache before the FIRST partial import-union/objects
entry in subsequent tool inputs. No cache/source/object/launcher is changed,
no extra workspace is made and no infrastructure is built. This is an explicit
dependency-selection/environment change, not an unchanged rerun. Pin selected
object hashes in receipts; focused composed replay, not coherent release rebuild.
