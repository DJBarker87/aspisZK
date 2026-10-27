# Pinned inherent-method selector limitation

XRg_003 exited zero and remained call-closed, but inventory found seven opaque release leaves, not eight. The typed inherent-impl selector did not match decode_k. No Aeneas invocation was run on that artifact. The original record and LLBC hash are retained.

Pinned Charon charon/src/name_matcher/mod.rs:268–271 explicitly implements `(PatElem::Impl(_pat), PathElem::Impl(ImplElem::Ty(..)))` as TODO / false. Corrected selector `crate::r1_wire::_::decode_k` uses one wildcard path element. It names the unique decode_k method in that module; the next inventory must confirm exactly the expected eight leaves. This is a selector-only change, not a tool/source/LLBC patch. The unsuccessful Charon invocation counts toward 12.
