# Attempt exclusions

K001: own runner requested absent template harness inputs. Launcher failed before prover execution. Charged one Kani slot; source snapshot list corrected. K002: compile-only failure because exact KMX generic allocator stub requires cfg(kani) allocator_api on the library root; added the cfg-only scratch attribute. No semantic pass. K003 onward use that corrected input. No frozen body changed.

L001 inspection; L002-L008 canonical powers replay passes with only standard axioms. These are local proof inputs, not composed row credit until native/control and ax2/model/caller gates pass.

L009 failed only because the final simp omitted the existing inside bound; corrected in L010, which passes. L011 inspection used two absent identifiers; corrected inspection L014 passes. L012 array roundtrip left List.map identity; corrected in L013, which passes. Failed elaboration outputs containing sorryAx are excluded entirely; only successful sources are proof candidates.

K019-K022: four distinct full-backing syscall shapes timed out, no credit. Reviews accompany K019-K021; K022 used one symbolic byte but still a full-sized backing allocation. This normalization shape is stopped; only bounded native windows plus a separately proved physical frame lift may replace it. K023/K024 establish the preliminary Prepared Result/error/scratch control facet, not full constructor closure. Before collecting further facets, the oracle transcript was expanded to retain and log the hash handle at every call; the earlier local facet remains historical, and the revised caller control is rechecked. No observer, writable static or multiplication gate is used.

Powers caller audit found N4 as well as N7/N29; K025/K026 extend the generic induction's native coverage to the complete deployed set. Source callee-domain review records this correction explicitly.
