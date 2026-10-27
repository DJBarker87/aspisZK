# Field and byte value laws

New accepted Lean source: LPi_Total, LPi_NatBase, LPi_CMProduct, LPi_FieldValues,
LPi_TowerValues, LPi_MixedValues, LPi_WriterValues. Each top has a printed audit.
All accepted audits use only propext, Classical.choice, Quot.sound. Failed
error-recovery sorryAx reports are retained and excluded.

Exact total emitted natural-coordinate laws now cover M31/CM31/QM31/WideExact
multiplication and mul_by_r on canonical higher-field inputs; M31 and
QM31.mul_m31 allow raw inputs. CM31/QM31 mutable serialization laws
allow arbitrary initial exact8/exact16 slices and raw limbs. They do not by
themselves establish native source-to-model association or whole leaf closure.

LPf_BaseMultiply and its three prerequisites were rebuilt unchanged privately.
Other inherited proofs are not reproved. No shared cache, shipped Rust, ELF,
security contract, carrier, failure event or top theorem changed. All scopes
were admitted exit0/allowed:true, serial 6G/8G/swap0/tasks64, Lean-M7000.
No Kani run yet. No native field multiplication is proposed.

The source import survey found an unrelated missing mathematical value closure.
A direct natural coordinate proof supplies the missing total value facts on the
actual FIo emitted arithmetic. The failed import exploration is excluded.

Top delta: zero. No joint top-premise inhabitant is claimed. Q.raw/reduced Q and
E emitted serialization remain exact open stage1 items in LPi_STUBS.md.
