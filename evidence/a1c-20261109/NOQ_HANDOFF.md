# NOQ handoff: A1 field X9 at the corrected host (Stream A, job NOQ_)

**The A1 field compiles, with no scaffold hypothesis left.**

```lean
AspisR1.NOQ_FinalCombined.field {W Tx} (L0 copy std) :
  RSL.TAS.NND_A1 (AspisR1.NOC_Run5bHost.S_host (W := W) (Tx := Tx) L0 copy std)
    NNH_Libraries.VL NNH_Libraries.P NNH_Libraries.C
  := NOQ_A1Assembly.field_of L0 copy std (fun c => AspisR1.NOC_Stage1Iff.iff345 c)
```

- Delivered-type `rfl` example: in NOQ_FinalCombined.lean (L005, exit 0).
- Combined import: the same file imports every NOM_ and NOC_ accepted root (including NOC_Stage1Inv, NOC_Stage1Conv and NOC_Stage1Iff) and all NOQ_ roots. 33 modules, one scope (L005).
- Raw ax2 (L006): ledger30's pinned walker NNM_ProofDriver, sha256 46ee271b…ca3c, the same binary as NOF_ L014/L018. For root `AspisR1.NOQ_FinalCombined.field`:
  - walked = collected = {Classical.choice, Quot.sound, propext};
  - 70581 reachable constants and 2282097 edges.
  - The list is in NOQ_audit/*.xz, with its sha256.
  - The eight passing ledger30 walker fixtures for this identical binary are reused, not rerun.
- Branch codex/cx-a1c-20261109, merged with research e6b16ae80de. Source revision of L005/L006: e6f9907af8e.

## Delivered constants (all axioms propext, Classical.choice, Quot.sound; savedBytes propext, Quot.sound)

| constant | statement | scope |
|---|---|---|
| `AspisR1.NOQ_WeakErrHost.modelRet1` | S_host (NOC).ModelRet1 c a r ↔ ∀ e p data, a = child1 NND_Carrier.error e p data → (∀ saved, r = .ok (nativeBytes saved) → model1 c p e.first data = .ok (.Ok saved)) ∧ (∀ error, r = .error error → ¬∃ saved, model1 … = .ok (.Ok saved)); by Iff.rfl | L001 |
| `NOQ_A1Assembly.IFF W Tx` | abbrev; exactly the type of NOC_Stage1Iff.iff345 (scaffold only) | L003 |
| `NOQ_A1Assembly.child1` | child1 NND_Carrier.error e p data = ⟨NND_Carrier.key p, NNH_ModelCarrier.accounts e.first, NND_Carrier.bytes data⟩ | L003 |
| `NOQ_A1Assembly.savedBytes`, `returned` | nativeBytes saved = bytes saved.deref; the returned arm r of TX1_345.Ref at child1 equals tx1Value ⟨…⟩ (NOC_Run5bCtx.envOf c), via NNH_ReturnsBundle.tx1_returns | L003 |
| `NOQ_A1Assembly.okT` / `errT` | the Ok clause from the ← side of IFF; the weak Err clause by contraposition of the → side | L003 |
| `NOQ_A1Assembly.field_of (h : IFF W Tx)` | the NND_A1 field above, with rfl example | L003 |
| `NOQ_A1Converse.field_of_conv (h : CONV W Tx)` | the same field with only the converse as hypothesis; Ok from NOC_Stage1Forward.ok345 through `sameSdk : NOC_Stage1Forward.S c = NOC_HostCtx.sdk c := rfl`. Not needed now; kept as a fallback | L004 |
| `AspisR1.NOQ_FinalCombined.field` | the hypothesis-free field | L005 |

Route of field_of:
1. intro the binders.
2. NOQ_WeakErrHost.modelRet1.mpr.
3. subst the child1 equation.
4. The EnvRep conjunct gives env = envOf c (NNH_Run5bCtx.env_unique).
5. `returned` gives r = tx1Value at the carrier form.
6. okT and errT apply.

Deviation from the brief, recorded: AMN.viaReturns1/toNND_A1 do not apply. S_host's ModelRet1 has the NNH_AcceptanceSig.physical shape, with ∀ e p data outside the conjunction, not AMN's withMin. The same happened for A2 (NOF_).
- The field is built directly, as in NOF_A2FieldCorrected.
- The type is the exact requested one (rfl example).
- okT and errT are the viaReturns1 obligations in the physical shape.

## Assumptions

- Discharged: the A1 model-transport field NND_A1 at NOC_Run5bHost.S_host.
- Retained: those already inside the merged modules used (NOC_*, NNH_*, NNV_*, NOM_*).
- Added: none.
  - IFF and CONV are definitions used only as scaffold variables. The shipped `field` has no hypotheses beyond L0, copy and std.
  - Exhibited is an unused binder.
  - EnvRep is a field binder, used only through env_unique.
- No Root0, Realizes-as-premise, hash-injectivity, success, representation or selector premise. The adversary/context is universal.

## Validation

- Six capped scopes (L001–L006), one at a time: 5 pass, 1 fail.
  - L002 failed because `open AdapterRw` inside namespace AspisR1 opened AspisR1.AdapterRw. Fixed with `_root_.AdapterRw` names. Uncredited.
- Caps: v4.32.0, `lake env lean -j1 -M7000 -DElab.async=false`, 180 s, MemoryHigh 6G / MemoryMax 8G / MemorySwapMax 0 / TasksMax 64.
- Every launch had admission allowed:true AND exit 0, scope count < 6, lean processes < 6, and disk >= 40 GB.
- Max peak RSS was 6990372 KiB (L006); swaps 0.
- Dependency objects are pinned by sha256 in each NOQ_Lnnn/receipt.json. The NOC_Stage1Iff.olean pin b2872443… equals NOC_OVERLAY.json.
- This is focused cached validation, not a frozen-release replay.
- Budget: 6 of 20 scopes, 0 Kani, 0 extraction.

## Note for NOC_ (observation, not an edit)

`sameSdk` holds by `rfl`: S c and NOC_HostCtx.sdk c are both the fixed-clock residual of NOC_HostSeed.m0. NOC_Stage1Iff instead proves it through sdk_at_slot/clockFree (slot clock); both compile.

## Overlay for G0 FINAL

Prepend /home/dombarker/project-offloads/codex-cx-a1c-20261109/NOQ_objects to NOQ_PATHS.json (NOC_objects first, then NOC_PATHS.json). Object hashes are in NOQ_OVERLAY.json.

target not yet established
