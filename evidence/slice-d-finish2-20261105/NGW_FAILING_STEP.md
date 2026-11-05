# NGW failing steps (live)

NGW_L002/L003: local proof import / canonicality definition mismatch. Corrected in L004, PASS. NGW_L006: Or orientation of List.mem_or_eq_of_mem_set; corrected in L011, PASS. NGW_L012: unreduced let pair in exact step equality; corrected in L015, PASS. NGW_L014/L018: reverse-loop induction tuple-match normalization and numeric projection elaboration; changed proof in L019, pending. All are elaboration failures; none a native/model counterexample or accepted proof. No failed theorem receives credit.

Stage2 polynomial: extraction and per-cell coefficient-add/reference laws now pass; the full same-byte native FIo-to-adopted FIn carrier/read transport and seven-step composed association remain missing callee laws. No row promotion.

Stage3 Weights::new K035: tool limit, 90-second CBMC timeout on regular_g0 with all point/factor arrays plus arithmetic/call logs. Replacement changes the packet into independent scalar-pair row, source point lookup and write-frame windows. No limit increase; original K035 excluded and never rerun unchanged. K036..K047 pass/fail as intended on the changed scalar-pair packets.
