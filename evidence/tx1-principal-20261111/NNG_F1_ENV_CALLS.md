# NNG-F1: fixed Calls would freeze the reservation reply

Target not yet established. This is a finding against an NNG provisional
interface, not an RSL revision-3 specification error or a shipped-source bug.

`NNG_Observed136.producer` accepted one `c : Calls` outside the universal Env
binder. Its `c.c8 : Prefix → Result Claims` therefore cannot change with
`env.reservation` at a fixed source Prefix. A revision-3 graph which returns
Err(Allocation) for reservation=false and its successful model value for true
cannot equal that fixed raw call at both environments. The older occurrence
lemmas requiring one fixed call to equal the field relation at EVERY Env were
valid implications but too strong for this intended installation. They are
support only and have never been used by a candidate or claimed row.

Replacement: `NNG_EnvObserved136.producer` takes `calls : Env → Calls`, and
chooses `calls env` at precisely the Env quantified by RowSpec. Its output
projection is fixed field-by-field by `NNG_Projection136.Representation`.
`NNG_EnvCallGraph136` and `NNG_EnvOccurrences136` conclude pointwise equality
with the matching VLib field at that SAME actual Env. The source law and field
graph need agree only at that Env. No reservation reply is fixed to success,
no caller domain is strengthened and no VLib field instance is constructed.

The exact emitted-tree association and interpreter proofs remain valid:
they quantify arbitrary Calls and can be applied to `calls env` pointwise.
The pending raw-to-Ref fold must use this Env-dependent target and these
pointwise occurrence laws, not the superseded fixed-Calls Target.
