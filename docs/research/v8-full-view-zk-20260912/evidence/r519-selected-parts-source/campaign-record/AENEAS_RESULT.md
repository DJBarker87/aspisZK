# R519 Aeneas translation result

The one authorized focused translation of the rewrapped Fun107 closure was attempted with the pinned R497 Aeneas binary. It exited 2 after 0.19 seconds, with peak RSS 68,464 KiB and swap 0. The tool raised `Invalid_argument "option is None"` at `Aeneas.FunsAnalysis.analyze_module...visit_rvalue`, `FunsAnalysis.ml:176`, during `init_fun_id_of_global` lookup. No Lean output was generated. This records a translator failure, not a source or Lean proof result.

- Target input: `R519SharedGammaPartsSelection.rewrapped.llbc`
- Input SHA-256: `4757453fd82b979c510025b2e83ae8ddd149014a3d1cbf0e753e4d3d36bc6d07`
- Captured source LLBC SHA-256: `600705e63cb7ba718e09a11e2da257c2fccf097173bfea00f294446265d32bc8`
- Source revision: `1d01ab5c3e43eac493f11b105fdaaf297e9b28cb`
- Aeneas binary SHA-256: `85a1037c1d2e675907c4a9c3b0b87e671633f9284775b1be8720f8f208b4086b`
- Unit: `aspis-r519-shared-gamma-parts.service`; `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`; aggregate reservation was checked before launch.

Complete Aeneas log, launch, receipt, and copied input are under `saved-output/`. No retry, translator edit, or Lean compile was made.
