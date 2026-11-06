# Own input corrections

L002/L003: inspection names corrected to AspisR1PublicPreparation, nonexistent lift name removed. L004/L005: own theorem indentation and ambiguous bind resolved; L006 passes. L008/L010: multiline record layout corrected; no proof theorem accepted from failing elaboration. L009 failed before submission because its imported TailVerified object had not compiled; it was never launched or resubmitted. No host infrastructure edits, timeouts or memory kills.

Runner copied from NLC and renamed for NLI workspace/budgets. Same or stricter admission, disk, serial guard, pinning, transport and retained-receipt checks. Config generator only authors own attempt inputs.

L012 initially refused by the local serial client guard while L011 was still collecting; no admission/scope launched. It ran only after L011 ended. Suffix batch traversal was found reversed during L019; the LOCAL batch parent was paused, L019 completed and its receipt was collected, then only the paused parent was terminated. No host scope was killed and no duplicate target launched. Traversal fixed to predecessor order.
