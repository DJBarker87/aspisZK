# Decode native stage

K003 iterator PASS (221 checks,3 unreachable): SAME framed/payload/selected-window pointer, enumeration index/count/end for caller N=1/28/29 and every fitting selected range of every framing length5..3717.
K005 scalar guard PASS (303): exact frozen row/checked multiplication/checked addition/get sequence on all row bytes, all usize offsets, caller N and every length5..3717; u128 spec includes overflow/error precedence.
K006 decoder PASS (223,1 unreachable): arbitrary32 bytes, row, every bounded selected index; exact four natural limbs, canonical/reject flag, SAME NonCanonical row/value. No high-half premise: decode_k intentionally reads only low16.
K007 typed output step PASS (266,3 unreachable): actual native N1 call, arbitrary canonical three-cell QM31 pre-state, selected cell, assignment to middle cell, both frames, no write on rejection. The canonical pre-state domain follows from zero initialization and every earlier K006 output; it is not supplied canonicality for input bytes.
K008 token PASS (132): actual Prefix::validated_record/record, all row bytes, distinguishable stored pointer/length entries, exact SAME row/framed carrier or InvalidRow. This checks the getter, not Prefix::parse, whose fixed row shapes/frame checks remain the upstream provenance.

K004 failed an unwinding assertion inside builtin memcmp on a32-byte u64-array assertion. No semantic credit. Replacement K006 compares four scalar limbs with unchanged10 unwind/caps/timeout. Own harness repair also uses scalar equality in K007. No source implementation change or unpaired stub. Complete raw logs retained.

Every run has fresh exit0/allowed:true reservation, offline optimized frozen441-package graph, unchanged frozen lock before/after and full source/tool/argv/time/RSS/swap receipts. No LPb stage is used. K003/K005/K006/K007/K008 compose only through the stated per-step/window/token association; whole leaf remains OPEN until Lean output/error/carrier joins and audits are green.
