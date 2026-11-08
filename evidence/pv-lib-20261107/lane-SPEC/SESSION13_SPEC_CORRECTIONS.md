# Session13 local correction — SPEC-C11

No frozen row statement, endpoint premise or T field is changed.

Before, the successful `CallbackRuntime.valueAnswer` native360 branch returned:

```lean
some ⟨.returned (.ok value), w, r.events⟩
```

This retains the entire pre-memory, even if the lower native reply wrote it.
`ArcPhysicalGap13.drops_physical_write` (55161) checks the branch with its exact
local conditions. `byte_conflict` distinguishes unchanged count byte1 from2.
The adopted fc8808eb binary e05bc increments the physical Packet count.
The independent lane-A v2 source-store increment does not update OWNER bytes.

After, `BoundNative13.core` and final `PrefixNative13` select
`ArcPhysical13.reply` before the legacy value-only adapter. Its operands come
from the actual source Arc, its registered physical backing, and the pre-count
in both planes. Unequal/unbound planes remain an explicit interpretation gap.
The physical update is the named8-byte increment; v2 alone updates source cells.
The literal binary JLE outcome is used on returned success; every nonsuccess
answer retains its status/events. `one_to_two` and `write_away` (55166) check
that local graph and exact byte frame. This is not a universal source/binary
refinement, original-entry reachability or full-joint contradiction. In
particular overflow/source threshold agreement has not been discharged.

Scope457 and the bool ACTIVE Cell replacement also have explicit physical
mirrors alongside the existing source actions. These are additional binding
work, not separately claimed checked contradictions of old full contracts.
No provider or old proved module is edited. The final native runtime retains
ordinary-native ghost framing on every returned adapter answer; only the
existing exact named allocation tokens bypass it.
