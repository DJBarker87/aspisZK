# NCF U04 bridge ledger

All fourteen slots OPEN. No native extraction component discharged.
S2 / deployed 100-bit target not yet established.

Frozen revision 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
Headline AspisR1.RPx_Deployed.deployed; digest/error op43/op44.

| Slot | Function | Owned caller / cohort op line | Reused evidence | Remaining |
|---|---|---|---|---|
| op15 | `validate_verifier_policy_v1` | 101 / 1376 | NCC K053/K054 full typed two-run | OPEN: actual SDK caller association with controls and Lean extraction component |
| op23 | `decode_pool_v1_pair_forest_terminal_request_v1` | 347 / 2688 | NCC K033/K034 len 0..321 | OPEN: arbitrary-length rejection plus actual SDK caller association with controls and Lean extraction component |
| op25 | `is_paused` | 195 / 1915 | NCC K041/K042; contract K055 | OPEN: actual SDK caller association with controls and Lean extraction component |
| op26 | `is_immutable` | 194 / 1910 | NCC K043/K044; contract K056 | OPEN: actual SDK caller association with controls and Lean extraction component |
| op27 | `is_paused` | 135 / 1536 | NCC K045/K046; contract K057 | OPEN: actual SDK caller association with controls and Lean extraction component |
| op28 | `is_immutable` | 134 / 1531 | NCC K047/K048; contract K058 | OPEN: actual SDK caller association with controls and Lean extraction component |
| op29 | `is_active_at` | 170 / 1762 | NCC K049/K050; NCF K002–005 contract/control/use pair; L003 exact cohort value | OPEN: actual SDK caller association with controls and Lean extraction component |
| op30 | `is_active_at` | 222 / 2068 | NCC K051/K052; NCF K006–009 contract/control/use pair; L003 exact cohort value | OPEN: actual SDK caller association with controls and Lean extraction component |
| op31 | `decode_verifier_registry_v1` | 177 / 1837 | NCC K025/K026 len 0..129 | OPEN: arbitrary-length rejection plus actual SDK caller association with controls and Lean extraction component |
| op32 | `decode_verifier_registry_entry_v1` | 200 / 1943 | NCC K027/K028 len 0..193 | OPEN: arbitrary-length rejection plus actual SDK caller association with controls and Lean extraction component |
| op33 | `decode_verifier_registry_v2` | 109 / 1404 | NCC K029/K030 len 0..257 | OPEN: arbitrary-length rejection plus actual SDK caller association with controls and Lean extraction component |
| op34 | `decode_verifier_registry_entry_v2` | 140 / 1564 | NCC K031/K032 len 0..321 | OPEN: arbitrary-length rejection plus actual SDK caller association with controls and Lean extraction component |
| op48 | `decode_master_box` | 261 / 2258 | NBX row/sequence/domain laws; NCF selected iterator write/frame and typed Box pairs | OPEN: original decoder two-run/frame, iterator-next/Box/error/allocator and actual SDK caller association with controls and Lean extraction component |
| op49 | `decode_checkpoint_box` | 286 / 2333 | NBX row/sequence/domain laws; NCF selected iterator write/frame and typed Box pairs | OPEN: original decoder two-run/frame, iterator-next/Box/error/allocator and actual SDK caller association with controls and Lean extraction component |

NCF_SOURCE_INVENTORY.json pins exact source lines and decoder first guards.
It is static inspection only. New local native/Lean components are recorded below; no whole slot closure is credited.
No XRn kit, extra trust, source adoption or changed statement is used.

## NCF component evidence and remaining native gates

- op15: K058/K061/K065/K067 pass their local/pilot checks, but K059/K066
  each fail an extra ghost-pointer precondition as well as the intended inverse
  postcondition. Both controls are INVALID; all policy/SDK pilot credit is
  withheld. K062/K068 are intended caller assertion failures. Extra ghost
  precondition and rejected/aliased fixture are not upstream domain coverage.
- op25–28: full typed NCC native getter contracts reused. Individual inverse
  postcondition controls and local contract-use/assertion controls K046–057.
  These local consumers are not the SDK authentication function.
- op23/31–34: K010–019 symbolic wrong-length pairs have initialized zero backing
  plus one arbitrary byte at arbitrary offset. Simultaneously arbitrary payload
  remains OPEN (K026 CAR failure, K027 invalid control, K028 compiler ICE).
- op48: K020/K021 selected iterator write/frame and K030–037 Box components.
- op49: K024/K025 corrected selected iterator write/frame and K038–045 Box
  components. K022/K023 use a wrong own capacity literal and are EXCLUDED.
- K001 and K029 are own compile/unwinding failures, not semantic controls.

No row is “instantiated by native function (ruling s)”: each still lacks the
complete actual caller association and per-slot extraction component. Selected
nth fragments do not establish the original iterator prestate/next relation;
Box pairs do not establish the decoder/account/allocator composition. All
remaining pure NBX induction/selection/retention results are reused unchanged.

## Final native allocation and caller findings

K069/K070 pass/fail the ACTUAL decode_master_box wrong-length result on valid
initialized symbolic-length inputs with one arbitrary payload byte. This
closes that local rejection component only; full successful decoder/Box joining
and full-payload representability remain OPEN.

All70 authorized Kani attempts are used. NCF_HANDOFF.md lists per-slot native
blockers and why no remaining independent Lean-only gate can discharge them.
No further native launch is authorized under this task.
