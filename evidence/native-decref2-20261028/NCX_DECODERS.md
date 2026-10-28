# Current registry decoder ledger

Status: OPEN. Frozen source 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387.
Headline AspisR1.RPx_Deployed.deployed; op33 registry and op34 entry.
Budget 40 Kani, 60 Lean. One admitted capped scope at a time.
No shipped changes; harnesses are scratch-only and delivered as patches.

The August extraction is excluded: current registry byte 7 is the PDA bump,
byte 248 is the ProgramData bump, and reserved bytes start at 249.
Current entry bumps are bytes 312 and 313; reserved bytes start at 314.

Stage 1: NCX_E002 extracts both current references with the NCV tool pins.
NCX_E001 is a rejected missing-Option-item extraction, not proof evidence.
NCX_L001/L002 compile Types/Funs (-M7000; capped host; exact receipts).
No external template was emitted. Safe casts preserve exact width; native
source correspondence and fixture evaluations remain OPEN.

Stage 2: NCX_Carrier roundtrip/surjectivity covers both complete records,
all four statuses and all twelve exact error variants (L003). NCX_Install
selects op33/op34 in missing.adapter and in the SDK, alongside NCV_Install's
op48/op49/op50; preserves outer failure/divergence (L004). These are dictionary
selection results, not a discharged AeneasExtraction/native P6 boundary.
Axioms are standard only; no hypotheses/trust items were added or changed.
