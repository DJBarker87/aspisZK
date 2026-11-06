# NJJ certificates

TX2:065 OPEN; target not yet established. No row/count promotion. Native semantic transport is P6/D188 option-A trust reclassification, never removal. All local positives below have matched controls; K080 is an unrun extra guard and adds no credit.

| Frozen/staged native cut | PASS | Matched semantic FAIL controls |
|---|---|---|
| NJJ_lib::any_step | NJJ_K005 | NJJ_K006 |
| NJJ_lib::chunks_step | NJJ_K007 | NJJ_K008 |
| verifier::NJJ_parent::header | NJJ_K009 | NJJ_K010 |
| verifier::NJJ_parent::weight_iterator | NJJ_K011 | NJJ_K012 |
| verifier::NJJ_parent::map_allocation64 | NJJ_K013 | NJJ_K014 |
| verifier::NJJ_parent::pending_window | NJJ_K017 | NJJ_K018 |
| verifier::NJJ_parent::flush_step | NJJ_K019 | NJJ_K020 |
| verifier::NJJ_parent::pending_start | NJJ_K021 | NJJ_K022 |
| verifier::NJJ_parent::pending_end | NJJ_K023 | NJJ_K024 |
| verifier::NJJ_parent::value_window | NJJ_K026 | NJJ_K027 |
| verifier::NJJ_parent::raw4_window | NJJ_K028 | NJJ_K029 |
| verifier::NJJ_parent::raw16_window | NJJ_K030 | NJJ_K031 |
| verifier::NJJ_parent::raw32_window | NJJ_K032 | NJJ_K033 |
| verifier::NJJ_parent::k_window | NJJ_K034 | NJJ_K035 |
| verifier::NJJ_parent::e_window | NJJ_K036 | NJJ_K037 |
| verifier::NJJ_parent::checksum | NJJ_K038 | NJJ_K039 |
| verifier::NJJ_parent::query_word | NJJ_K040 | NJJ_K041 |
| verifier::NJJ_parent::state_roots | NJJ_K042 | NJJ_K043 |
| verifier::NJJ_parent::gamma_alpha | NJJ_K044 | NJJ_K045 |
| verifier::NJJ_parent::rho | NJJ_K046 | NJJ_K047 |
| verifier::NJJ_parent::semantic_slot | NJJ_K048 | NJJ_K049 |
| verifier::NJJ_parent::z_slot | NJJ_K050 | NJJ_K051 |
| verifier::NJJ_parent::claim_rhs | NJJ_K052 | NJJ_K053 |
| verifier::NJJ_parent::power | NJJ_K054 | NJJ_K055 |
| verifier::NJJ_parent::weight_slot | NJJ_K056 | NJJ_K057 |
| verifier::NJJ_parent::tail_guard | NJJ_K058 | NJJ_K059 |
| verifier::NJJ_parent::prepared_tail | NJJ_K060 | NJJ_K061, NJJ_K062 |
| verifier::NJJ_parent::accumulator_tail | NJJ_K063 | NJJ_K064, NJJ_K065 |
| verifier::NJJ_parent::resume_allocation_site | NJJ_K066 | NJJ_K067, NJJ_K068, NJJ_K069 |
| verifier::NJJ_parent::pending_allocation_site | NJJ_K070 | NJJ_K071, NJJ_K072, NJJ_K073 |
| verifier::NJJ_parent::pending_stop | NJJ_K074 | NJJ_K075 |
| verifier::NJJ_parent::finish_stop | NJJ_K076 | NJJ_K077 |
| verifier::NJJ_parent::weights_stop | NJJ_K078 | NJJ_K079 |

All per-run graphs match the frozen lock and deployed feature closure; all post-run lock hashes are unchanged. Same-harness names are retained. No contracts, stub_verified, writable static, field-product proof, Option<fn>-dependent result or custom copy stub. Exact KMX sources and patch are checked each time.

The native-to-cut transcriptions are NJJ_Cuts (pending payload/end and weights), NJJ_Constructors (all Prepared/Accumulator fields), and the source-body specialization NJJ_Common. Native row windows are lifted by NJJ_RowWindow over supplied KMX laws; NJJ_PendingStep derives the complete typed step from the literal emitted body; NJJ_Pending supplies finite induction. NJJ_ResumeDomains derives every entered read bound and complete byte/cursor/frame Result. NJJ_Value projects the actual emitted value at arbitrary index to a single row, and NJJ_Flush gives every output cell and canonicality. These lemmas do not invent missing parent argument observations; see REMAINING.

Full-source inputs are retained once by sha256 in NJJ_inputs and NJJ_INPUTS_INDEX.json; each receipt lists exact source hashes, dependency objects, source revision, cap, time/RSS/swap and axioms. No failed Lean version is selected.

Copy-dependent positives use the supplied exact patch and the controls in this table. Source/domain qualifications remain those of NJJ_CUTS.md. In particular, the checksum native scope requires proof57607/public≤1880; its unrestricted-root domain is not proved. Receiver/backing observations missing from selected parent cuts remain OPEN, not extra assumptions.
