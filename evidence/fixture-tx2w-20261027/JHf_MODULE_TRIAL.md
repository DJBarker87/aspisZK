# Single module-system SHA experiment

Attempt JHf_TX2_047: JHf_SHAFacade.lean; exit1; wall0.6090605450444855s; peakRSS1575920KiB; swap0. The receipt pins source revision/hash and tool binary. Source uses the Lean module system, a private JGz_Realizes import, and public boundary/type imports.

Exact error: `cannot import non-`module` JFn_HashBoundary from `module``. This stops before importing the full SHA closure. The measured RSS is the failed facade/importer's RSS, NOT a successful full verifier/SHA union. The downstream JHf_SHATrial importer did not run; its RSS is unavailable. Existing dependencies may not be rewritten under this job's new-modules-only rule.

This is the ONE requested module-system trial; no unchanged retry, nonmodule import-union rerun, cap increase, alternate proof axiom or module conversion of existing sources is performed. Keep the exact named JFn_HashBoundary.Realizes JFp_SHADigest.digest hypothesis in every full verifier consumer. The failed facade and uncompiled downstream source are retained as unchecked text at final handoff and receive no proof credit.
