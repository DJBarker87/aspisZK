Item7 CLOSED in NNQ_COMBINED_IMPORT, L030. batch_loop_eq is induction on
fuel from existing Port9OR_BatchLoop.body_dictionary, then batch_tree_eq,
batch_values_eq and batch_source_eq compose it into batch_eq/batch_stage_eq.
These are equalities for arbitrary dictionaries, stronger than shared-copy
irrelevance, with no additional caller-domain or success premise.
L029's last two wrappers failed because the rewrite was beneath a local let E;
no failed module/object credit. L030 reduces that let before the named source
rewrite and includes these six declarations in the final combined module.
The rejected standalone NNQ_Batch source and uncompiled NNQ_FirstCode proposal
are .lean.txt archives; neither is imported. All earlier accepted modules are
imported transitively by NNQ_PreparePort. The final combination additionally
imports NNH_ContinuationCombined (run5 S0), NNH_S5FocusedHost (run5 latest
focused host), and the unchanged DGP_HostDigest statement.
L030: exit0,4.474146s,6707244KiB RSS,swap0, all15 printed roots standard-only.
No final frozen manifest replay, release replay or headline result is claimed.
Budget final:30/30 actual scopes,16 pass,14 proof/import/elaboration failures;
0 Kani,0 extraction. Deterministic heartbeat failures are retained as failures,
never cap increases. No wall-time timeout or memory kill occurred.
NNQ_validate.py verifies source/accepted-object receipt associations, admission,
resource limits and every printed accepted axiom list. Initial local validation
snippet had a syntax typo; the committed validator corrects it without reducing
checks. No additional Lean scope was used by this bookkeeping validation.
