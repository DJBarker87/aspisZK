# f21 complete statement, D985 / session 4

PV_LIB_SLICE_Spec_f21 now states Pre, MachineSpec, Post and Contract : Prop.
Focused 49924 passes. Contract is deliberately unproved. D985 accepts the
package Success.vector defect checked in session 3: construction length zero
is replaced by the actual SliceToVecFinish.vector with final length n, tied
to the same fresh header (also for positive n). Frozen prose is unchanged.

The literal pre_comparison, machine_implies_package, pending_implies_old,
no_false_pending11, final_length and package_success_forces_zero comparisons
remain compiled. SESSION3_f21_COMPARISON.md retains the detailed package
comparison. FullFrame adds the previously missing heap frame outside fresh
allocation intervals and the exact lower-continuation suffix. FreshByte uses
only allocator metadata at reached source prefixes, not changed-byte search.
SourceFrame preserves shared bytes on every non-abort arm. Abort erases all
state. Reference covers the first own completion, fault or actual pending
answer, and every prefix of infinite execution. All payloads/worlds/events
are those of the same named source interpreter, with no success restriction.

The former full-contract gate conflated statement completion with proof.
Primitive adequacy, the D877 graph-summary transport, frame preservation and
Contract itself remain proof obligations; they do not block this statement.
No primitive semantics, row proof or joint witness is claimed by this file.
49923 was a local projection typo (.world.allocator instead of
.world.world.allocator); exact failed input and receipt retained. 49924 changes
that source projection and passes under the unchanged caps.
