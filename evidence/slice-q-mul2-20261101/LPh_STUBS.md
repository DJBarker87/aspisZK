# NEI multiplication treatment

No `kani::stub` replaces a field multiplication in these packets. Kani never
executes field multiplication. Full actual emitted arithmetic is related to the
coherent probe dictionary by NEI_FieldScalar/CM/QM/Wide, with caller domains in
NEI_LineDomains and NEI_CircleDomains. NEG product laws are reused.

| Native abstraction | Named Lean law | Domain / qualification |
| --- | --- | --- |
| K007 local `ProductLog` bounded reply, same lhs/rhs, no static or function pointer | `NEI_PrefixProduct.actual`, `NEI_PrefixProduct.specialize` (L031) | Every pair of raw U32 words; actual emitted and prefix callee return `ok reply`, reply.val = lhs.val * rhs.val mod 2147483647 and reply.val < 2147483647. Native universal cut specializes to this exact reply. |

This is an overapproximation/specialization table, not credit for an unstated
native stub. K008 is its matched failing argument control. The prefix native
append/frame remains a separate obligation; no multiplication theorem discharges
it. No unpaired field stub or old NEB native credit is admitted. Existing NEG
ProductAbstraction for dot products remains an imported model law; no native dot
product step is newly credited here.
