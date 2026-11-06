# NJN retained failed steps

Target not yet established. No rejected receipt is a certificate.

* L001: Charon exit 0, Aeneas exit 2, InterpBorrows.ml:2731 on
  NJN_reference.rs line 23 (guard drop's same-cell counter branch).
  All twelve roots were supplied in the single extraction. No Lean output.
  One authorized extraction consumed; no rerun or tool modification.
* K001–K004: compiler E0597 in the wrong-cell control: both AccountInfo
  arguments unnecessarily shared the payload lifetime. No semantic verdict.
  Corrected the control to quantify the two accounts' payload lifetimes
  independently; K005–K008 use the corrected source and unchanged properties.
  The initial queue incorrectly continued after compile rejection; later queues
  stop on missing VERIFICATION, and all four rejected attempts count as spent.
* L003/L004/L005/L010: own record-layout/parser and frame simplification
  errors. Failed output contains elaborator sorryAx placeholders and is EXCLUDED.
  No source contains sorry/admit/axiom. L012 replays the repaired complete file.
* L008: simplifier normalized the numeral before matching symbolic hypotheses.
  Replaced broad simp with exact if_pos/if_neg rewrites; L011 passes.

The native SDK contracts currently target exact one-call wrappers, not attributes
on registry methods. They preserve actual typed Ref/RefMut across the call and
exercise actual Drop. This distinction and the bounded constructed prestate
remain explicit; no universal SDK substitution certificate is claimed.
