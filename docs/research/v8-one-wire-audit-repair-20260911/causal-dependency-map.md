# Causal dependency map

| Object | Actual source boundary | Must precede |
|---|---|---|
| C1 root/word | before lambda/chi | OOD, gamma and responses |
| C2 root/word | after lambda/chi | gamma and responses |
| claims | before OOD points | OOD answers and gamma |
| OOD answer vectors | each follows its point | gamma |
| gamma | after both OOD vectors | inactive/kappa |
| inactive / kappa | after gamma | tau/response0 |
| public functional/claim / tau | `freeze` | response0 |
| response0 / alpha0 | fields 417..422 | final256/q22 |
| final256 / q22 / rho | fields 441..696 | later responses |
| response1/2/3 | fields 423..440 | respective later alphas |

Existing log inclusion does not prove these cutoffs, prefix nesting, retry
accounting, or Fiat--Shamir freshness.
