# Attempt exclusions

K001: own runner requested absent template harness inputs. Launcher failed before prover execution. Charged one Kani slot; source snapshot list corrected. K002: compile-only failure because exact KMX generic allocator stub requires cfg(kani) allocator_api on the library root; added the cfg-only scratch attribute. No semantic pass. K003 onward use that corrected input. No frozen body changed.

L001 inspection; L002-L008 canonical powers replay passes with only standard axioms. These are local proof inputs, not composed row credit until native/control and ax2/model/caller gates pass.

L009 failed only because the final simp omitted the existing inside bound; corrected in L010, which passes. L011 inspection used two absent identifiers; corrected inspection L014 passes. L012 array roundtrip left List.map identity; corrected in L013, which passes. Failed elaboration outputs containing sorryAx are excluded entirely; only successful sources are proof candidates.
