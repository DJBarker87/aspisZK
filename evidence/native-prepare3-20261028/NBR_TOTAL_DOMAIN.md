# Digest totality is a model condition

NBR_BlockConstruct.Total D is exactly `forall hash parts, exists reply, D.digest hash parts = ok reply`. NBR opening/material/query constructors and the top returned-input theorem retain this condition. They construct linked events from a total MODEL digest, rather than take preselected local traces as input.

The Rust Digest32 return type alone does not establish this condition for every Aeneas ABI input or arbitrary request. No native digest, allocation, panic, request-validity or runtime effect theorem is discharged by this model definition. The NBC lane must supply reached-request/native-call correspondence (or a justified total model completion together with validity of every reached request). It must identify identical ordered request bytes, replies, state, failures and effects. This is an explicit native correspondence dependency, not a new cryptographic or headline trust item. No headline premise is removed.
