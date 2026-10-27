# XRk audit notes

Target not yet established. This is an isolated external-model/ABI continuation,
not a completed source refinement. All twelve source/reference P6 bridges OPEN.
No crypto assumption, trust item or top premise is discharged by a model definition.

L013: no Lean invocation occurred. The unchanged S2W runner correctly refused a
missing XRk_ABI object after L012 failed. The orchestration mistakenly requested
a dependent module too soon. No launcher repair/bypass occurred. L014 fixed
the local Aeneas-do syntax, built the predecessor, and L015 then elaborated the
changed dependent source. The refused launch is conservatively charged to the
100 allocation limit. Its launcher log is retained; no compiler receipt exists.

Standalone Kani harnesses do not modify the shipped cfg(kani) modules and do not
trigger ELF rebuilds. The initial multiplication timeouts are retained, not
credited as counterexamples. K003 onward uses the narrowed arithmetic split.

L076 is the second orchestration refusal, not a compiler invocation: a dependent
geometry module was requested before reading L075's failed arithmetic proof.
The existing runner correctly rejected its missing predecessor object. This is
charged to the allocation budget and its log is retained. The geometry measure
was then changed to use the iterator's own length representation; L077 passed.
No runner, admission or monitoring infrastructure was changed or bypassed.
L075 recorded one aggregate-reservation refusal (48 GiB already reserved),
waited three minutes, then passed admission at its second barrier invocation.
