# Retained failing steps

No timeout, memory kill, cap increase, Kani or extraction attempt so far.

- L001/L002: canonical nominal constructor aliases do not export constructors
  through their alias namespace. Fixed explicit Variant/Error/Phase owners in
  the NHT retarget map. L004 passes the intermediate common body.
- L003: own-input prelaunch failure: missing predecessor object. No scope or
  Lean launched. The complete traceback is the local tool result; admission
  retained. Continued after repairing and compiling predecessor.
- L005/L006 replace the intermediate port with exact emitted transparent
  constants/standard helpers. This is a source change, not a repeated replay.
- L007: own retarget script imported Constants instead of EmittedCommon after
  header repair. Fixed import; L009 passes.
- L010: rewrite left a reflexive goal; added explicit rfl. L012 passes.
  Failed L010's sorryAx output is EXCLUDED, never an accepted proof.
- L017: missing local E abbreviation in the new round adapter; fixed explicit
  canonical carrier abbreviation. L018 then failed before submission on the
  absent predecessor object. No theorem/object from either failure is accepted.

All failed candidates and exact snapshots are retained in attempt directories.

- L021: an extra solved-goal bullet in finish composition. Removed; L022
  passes. L029/L030 then narrow round1 to the SAME successful first reply;
  this replaces a stronger universal native-cut premise before final selection.
- L023: polymorphic adapter function equality needed explicit @ applications.
  L024 passes; no native slot claim follows from model installation.
- L025: query Error/Phase nominal carriers differ from VTop's Adapter owners.
  Added injective total NHT_ResultPort and release-compatible NHT_PhasePort,
  preserving every payload/error/fail/div; L027 passes mapped query installation.
- L040: malformed multiline record in own tail definition. Repaired layout;
  L041 passes the exact Vec writeback factorization.
- L042/L043/L045: initial constant proofs did not unfold generated irreducible
  names / could not reduce platform-dependent checked Usize operations. Replaced
  by existing symbolic checked add/mul laws and a new checked-sub law. L048
  exposed sub_spec's conjunction postcondition; L049 fixes that exact signature.
  L050 proves all eleven source constants with standard axioms. No kernel
  normalization of a recurrence or large enumeration was attempted.
