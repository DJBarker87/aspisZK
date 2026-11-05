# NIO failures and replacements

K001: own no_std input error; alloc::rc repairs std::rc. The clone window also separates the uniqueness loop under rule B. No credit to K001.

K022/K023: own stub generic-arity mismatch for AccountInfo assign/resize. Early-bound lifetime repair retained in NIO_native_prepare.py. Neither compiler rejection is a semantic control.

K024: whole actual close_program_account_v1, arbitrary balances and one-byte payload, assign/resize cut stubs; CBMC TIMEOUT at 90 s. K025: a distinct shared-data rejection prefix of that actual function also TIMES OUT. Neither earns credit. No cap/timeout increase; no unchanged replay. Remaining close steps must be isolated before any new run. The original failed extraction is still NIK_E001; it is not retried here.

Missing callee law, not discharged: assign and resize are outside S2TrustedSdkBorrow's fifteen approved fields; their illustrative cut oracles have no paired actual model law. No positive from this family may be promoted to a complete caller certificate.
