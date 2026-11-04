# Excluded attempts and repairs

* L001: accidental import of original ARU_SelectorPure requested missing
  PAln_Public in the old horizontal forest. No proof ran. Repaired the OWN
  new module to import only NGK_COMBINED_IMPORT, whose RPz8-retargeted owners
  already provide the needed declarations. No original/shared module edited
  or rebuilt. This changed the dependency graph for L002.
* L002: scalar coercion normalization in suffix proof: 688#usize.val versus
  Nat688. Added a local `change 688 <= finish.val at ordered`; L003 passes.
  Recovery sorryAx printed by failed elaboration is excluded, never credited.
* L005: notation quotation precheck rejected a projection in a local notation,
  and dotted notation for local ops. Expanded the source-outcome expression
  and parenthesized ops projections; changed source L006 passes. No option,
  recursion/heartbeat, axiom, hypothesis or target weakening was added.
* Local audit-setup script initially read a sparse-unmaterialized NFA walker
  file. Used git show HEAD:path to compare immutable source bytes instead.
  No scope was launched by this local input failure.

No timeout, memory kill, transport failure, admission refusal or unchanged
retry occurred. Only source/dependency fixes above were recompiled. No Kani,
extraction, nonstandard-axiom, writable-static or copy-dependent native credit
was introduced. L014's combined import adds the direct persistence corollary;
it is a dependent proof target after L013, not a repeated unchanged regression.
L015 audits only that new root, preserving L012's unchanged17-root audit.

Own closure-pin validator initially required NGR_COMBINED_IMPORT itself to be
in the new closure. The new final aggregate imports NGR_HistoryPersist directly,
so that unused one-module aggregate is outside the target closure. The repair
permits ONLY this exact missing .olean, records it as not_in_target_closure,
and still rejects every missing shared dependency or changed hash. No Lean
replay or declaration was changed, and no proof credit relies on this absence.
