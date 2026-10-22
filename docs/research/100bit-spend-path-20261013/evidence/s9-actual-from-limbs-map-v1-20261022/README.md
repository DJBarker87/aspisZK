# Actual attempt7 `from_limbs` carrier map

This focused proof copies the actual generated `WideExact.from_limbs` body and proves its `Result (Option _)` map into the retained owned representation equals the owned decoder on the same limb array. It uses the explicit carrier map and the previously checked owned `from_limbs` map.

The packet pins the attempt7 generated `Funs.lean` and Rust source snapshot. It establishes a theorem about that extracted Lean body, not compiler binary refinement or deployed runtime behavior.
