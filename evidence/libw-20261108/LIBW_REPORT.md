# LIBW: per-Env registration of the weak TX2:064 law (TGB-1)

Target not yet established. This job changes a registration only. It changes no
RowSpec, Dom064, caller clause, trust row, frozen source or security metric.

## Problem (TGB-1)

`LIBB_V2Star.weak H d hash world` registers `NNC_ObservedLaw.w H d hash world`.
That law ignores its `Env` argument and fixes one hash model `H`. The canonical
law is read at `LIBB_PartitionEnv.H env` and `LIBB_PartitionEnv.digest env`
(`LIBB_Tx2Auth.native`). So the same host `I.f064` cannot refine both laws
at every Env.

## What LIBW_WeakPerEnv.lean states

- `wEnv world pub proof ck := fun env o => NNC_ObservedLaw.w (LIBB_PartitionEnv.H env)
  (LIBB_PartitionEnv.digest env) () world pub proof ck env o`. This is TGB-1's fix
  verbatim, with `X = Unit`.
- `wAny Ambient := ∃ world, wEnv world …` per observation. The canonical `native`
  holds at every world, so the weak law should not have to pick one caller frame.
  `refines_any` transports any fixed-world refinement to `wAny`.
- Registrations `weakEnv world` and `weakAny Ambient` are `TAS.lib LIBB_V2Star.library
  (fun _ _ => True) _`. They are the same V0, VErr and debug, and are `rfl`-equal to
  `TCK.weaken`. `weakEnv_specialised` is the pointwise identity with
  `NNC_ObservedLaw.w` specialised at each Env. `canonical_unchanged` checks that
  the canonical registration is unchanged.
- `writeFree`, `writeFree_any`: `TAS.WriteFree` at every argument, with no premise.
- `refines` / `refines_any_of_rep`: `TAS.Refines064 LIBB_V2Star.library f064 (fun _ _ => True) _`
  at every Env, from `HostRep` / `HostRepAny`. These say that the host observation equals the
  rendered native 064 run at the Env's own `H`/`digest`, which are the carriers the
  canonical `native` already uses.
- `assemble`, `assembleAny`: exact `TAS.NNC_G1a S L LIBB_V2Star.library VL I`. The only
  inputs are the host representation and the `okHeader` field.
- `okHeader_of_oracle(_any)`, `okHeader_field`: `okHeader` follows from a per-Env
  `CheckpointBytes5Inputs.Oracle` (`OracleEnv`) and a per-Env header representation.

## Retained or new obligations (not discharged)

1. `HostRep`/`HostRepAny` for the actual `I.f064`. This is the host interpretation
   that NNC_REMAINING already names.
2. `okHeader`. `OracleEnv` quantifies over all part lists. `LIBB_PartitionEnv.H env`
   always applies the three-part C04 partition, while the resume digests
   (singleton proof/public parts and the checksum parts) are not C04-shaped. So
   `OracleEnv` requires `env.sha256` to be invariant under repartitioning, which is
   not assumed. Expected fix: an Oracle restricted to the three resume calls (or
   separate C04-model and resume-header hashes) in `NNC_064Weak.accepted_header`.
   This is a TGB-1 follow-on (call it TGB-1b), found by inspection only.
3. Downstream re-specialisation: LIBB_V2Star/LIB_FullInstances consumers,
   NMS_R2Weak241 and NMV_ (TGB-6), at `wEnv`/`wAny`.

## Validation

Not compiled. The imports exist only as host objects (the LIBB_L344 LEAN_PATH), and
no local olean closure exists. `LIBW_compile_host.sh` is the exact single-file host
recipe: LIBB_L344 environment, cgroup 6G/8G/swap0, `-M7000`, and an acceptance check
on exit status, errors and the 19 `#print axioms` lines. The file has no sorry and
no axiom declaration.
