# Observer reconciliation

NDR_L001 validates the first adaptation with standard axioms only (3.800 s,
3,841,008 KiB RSS, swap 0). No cryptographic or adaptive execution premise is
discharged.

## NDO_JGi_FinishFields.source

Before: `(obs : Option (verifier.Phase → Result Unit))`, with premise
`FinishModel.finish R B D pub pre before challenges obs = ok (.Ok out)`.
After: `(obs : Option (RPz7_PhaseIso.Phase → Result Unit))`, with the identical
premise and conclusion. `NDO_PhaseIdentity.retainedCarrier` identifies this
carrier with the historical FirstCaller.Phase; the imported producer's nominal
verifier.Phase is distinct. All other quantifiers and proof bytes are unchanged.
This restores the historical quantification; it does not transport an execution
from the producer carrier. New direct import: NDO_PhaseIdentity.

The remaining adaptations and the 23 upstream differences are tracked below
as validation advances. Non-None producer observers require a proved execution
transport at producer/model comparison boundaries; callback round trips alone
are not that transport. No such new adaptive execution result is claimed.
