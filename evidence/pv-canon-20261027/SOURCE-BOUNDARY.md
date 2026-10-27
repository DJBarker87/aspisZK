# Source association boundary

The consumed `ProverRwP7CurrentFieldSource` from codex/pv-extract-20261027
contains the candidate `field::ct` implementation, with source annotations at
field.rs:3279 and field/ct.rs. The assigned research worktree's frozen
crates/aspis-core/src/field.rs instead contains the checked two-fold reducer
and feature-selected R91 add/sub branches; there is no field/ct.rs here.
This is expected candidate-cohort separation, not permission to overwrite
shared env-J sources or to claim the candidate module is the frozen source.

The new current_* theorems prove canonicality of the specifically named
extracted definitions. Their existing `ProverRwP7CurrentBaseBridge` equality
connects these definitions to the retained release field model. Discharging
P_installed must still identify that model/installation with the actual frozen
caller at its source revision and build features. The source identification
work merged into research is consumed as evidence, not silently replaced by
module names containing “Current”. No unconditional deployed claim follows
merely from compiling these modules.
