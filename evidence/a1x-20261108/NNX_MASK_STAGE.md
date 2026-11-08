# X3 symbolic mask gathers

Accepted NNX_C1Gather.source (L017) and NNX_Mask10.source (L018)
prove the exact 16/10 FinishModel callback gathers on arbitrary canonical
Claims, with no concrete claims evaluation and no success/representation
premise. NNX_ClaimIndex.source (L012) is the symbolic bounded row-zero getter;
NNX_ArrayRead.source and NNX_Gather.loop/array isolate generic reads/gathers.
All accepted printed axioms are standard only.

L005's generic gather residuals were repaired at L006 by explicit Option read
normalization and subtype reflexivity. L007-L008's WP specialized array-length
approach is retired. L009-L010's specialized simp-only read approach is
retired; the replacement isolates a generic bounded source read (L011) and
uses explicit Result rewriting (L012). L013-L014's direct get!/Option
normalization is retired; use the named core bounded-get theorem instead.
L015 fixed the qualified theorem arguments; L016 exposed only Fin.cast.val
reflexivity, completed explicitly in L017. Caps, heartbeats and timeouts stayed
unchanged; none of these was a resource timeout or memory kill. Every failed
source and diagnostic is retained; failed printed sorryAx lines are not credit.

The full fixed FinishModel.finish result, semantic slot, prepared front and
A1 body composition are not yet established.
