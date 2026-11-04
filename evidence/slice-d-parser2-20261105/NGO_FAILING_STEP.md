# Failing steps (no closure credit)

L004/L005: API discovery requested absent lemma names. Corrected discovery modules, not prover/infrastructure failures.
L008: local proof names/binder scope errors in exact chunk schedule; L009 corrects these and passes.
L011: E001 generated NGO_QRef.Funs applies U32.wrapping_shl to i32 shift literals, rejected by the selected Aeneas API. Tool emission/library interface mismatch. E002 isolates the same scalar expression with explicit u32 amounts 8/16/24; native bit values and shift positions are unchanged. No whole-call success premise or cap increase.

K001: own scratch-input omission: frozen docs/research path crates absent before metadata. No Kani process started, no proof verdict. NGO_PATH_DEPENDENCIES pins the restored immutable inputs; graph validation is unchanged.

K002: missing frozen workspace members, stopped at metadata; K003: missing immutable tools include, stopped in compilation. NGO_add_dependencies.py now restores the complete recursive manifest/member closure and retained includes. K004: Kani compilation needs allocator_api crate feature for the exact KMX stubs; added only cfg(kani) crate attribute in scratch, as predecessor did. No solver verdict or timeout in these attempts. Unreached pre-existing static harness warnings have no credit.

L026 compiles BitPack using bv_decide, but prints pack._native.bv_decide.ax_4. EXCLUDED: this violates the standard-axioms rule, and no downstream bridge may rely on this object. Replacing reflection with symbolic bitvector rewrites under unchanged caps.

L046: no compiler launch; own input import name was historical RawActualDecodeKMainAdapter, not coherent FIq_S_RawActualDecodeKMainAdapter. Counted conservatively. Changed only new NGO module import names to canonical owner; no existing module or object repaired.

L088: combined cohort import FAILED: ExtractedDigest32Transcript imports duplicate AspisR1PublicPreparation.TranscriptStep.readParts already owned by RPz7_ExtractedDigest32Transcript. Classification: historical import/callee-owner association, not a cryptographic mismatch. Canonical retained adapter is RPu_FIq_S_RawActualDecodeKMainAdapter. NGO_CanonicalPort retargets only the three own proof bodies in a single new module; old standalone modules are excluded, never shadowed. Two remaining compiler slots are L089/L090. An optimized C-only ax2/scan scope is charged conservatively as the final Lean/support slot after reconciling L046 as no-launch (not a compiler run). No budget cap is raised: 89 actual Lean compiler runs plus one C audit <=90; L046 remains separately recorded prelaunch evidence.
