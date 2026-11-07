/-
TCK_WeakRoot0: the Root0-free instance of the RSL TX2 verifier interface.
Core Lean only; imports the RSL_ package (evidence/rowspec-lead-20261107).

Purpose (TCK_REPORT.md, gaps G1 and G2).  The canonical RSL instance of
`V2Lib` sets `Root0 := NLP_InputDomain.Root0` and `tx2auth := NMN_064` law,
so RowSpec_241/240/221/213 hold only on the Root0 domain.  The top assembly
needs two Root0-FREE facts about the actual TX2 chain:
  G1  actual TX2 acceptance implies the resume digest check passed
      (so that NMF's "Root0 or charged collision" can be derived from the
      native run instead of from the headline's `extraction` binder);
  G2  every non-selected ASQ8 invocation writes no account data
      (the per-invocation effect required by `game.recorded`).
Both are obtained by instantiating the SAME parametric RowSpecs with a weak
interface: `Root0 := True` and `tx2auth := w`, where `w` is a law that the
actual TX2:064 satisfies on the three extents alone.  This module proves
that, under that instance, the own-input domains of 241/240/221/213 carry no
Root0 clause at all (240 and 213 become unconditional), so a parametric fold
yields an unconditional weak root.  It proves nothing about the frozen code:
the weak 064 law `w` and the parametric folds remain the owning jobs'
obligations (see TCK_REPORT.md).  Target not yet established.
-/
import RSL_TX1_330
set_option autoImplicit false

namespace RSL.TCK
open TX2_241 (V2Lib Dom064)

/-- The weak TX2 verifier interface: same error carrier and debug printer,
Root0 replaced by `True`, TX2:064 law replaced by `w`. -/
def weaken (V : V2Lib) (w : Bytes → Bytes → Bytes → Spec (Except V.VErr Unit)) : V2Lib :=
  { V with Root0 := fun _ _ => True, tx2auth := w }

/-- Under the weak instance TX2:064's domain is exactly the three extents. -/
theorem dom064_weaken (V : V2Lib) (w : Bytes → Bytes → Bytes → Spec (Except V.VErr Unit))
    (x : Bytes × Bytes × Bytes) :
    Dom064 (weaken V w) x ↔
      (x.2.1.length = PROOF_BYTES ∧ x.2.2.length = CHECKPOINT_BYTES ∧ x.1.length ≤ STATEMENT_BYTES) := by
  simp [Dom064, weaken]

/-- TX2:241's domain reduces to (D1) snapshot consistency. -/
theorem domain241_weaken (V : V2Lib) (w : Bytes → Bytes → Bytes → Spec (Except V.VErr Unit))
    (a : TX2_241.Args) (h : ∀ x ∈ a.accounts, TX2_241.Consistent x) :
    TX2_241.Domain (weaken V w) a :=
  ⟨h, fun _ _ _ _ _ _ _ _ _ _ => trivial⟩

/-- TX2:240's domain is unconditional. -/
theorem domain240_weaken (V : V2Lib) (w : Bytes → Bytes → Bytes → Spec (Except V.VErr Unit))
    (a : TX2_240.Args) (s : SdkState) : TX2_240.Domain (weaken V w) a s :=
  fun _ _ _ _ _ _ _ => trivial

/-- TX2:213 / TX1:330 entry domain is unconditional under the weak instance,
for the deployed stage1 packet (TX1:344's domain is `True`). -/
theorem domain213_weaken (V : V2Lib) (w : Bytes → Bytes → Bytes → Spec (Except V.VErr Unit))
    (VL : VLib) (P : PreparedNew VL) (C : TX1_345.S1Lib VL)
    (a : TX2_213.Args) (s : SdkState) :
    TX2_213.Domain (weaken V w) (TX1_344.asStage1 VL P C) a s :=
  ⟨fun _ _ => domain240_weaken V w a s, fun _ _ => trivial⟩

/-- Consequently a weak entry root is unconditional: every instruction and
every entry state is covered, with no Root0 or headline clause. -/
theorem entry_weak_unconditional (L : PoolLib) (D : DeployedIds) (V : V2Lib)
    (w : Bytes → Bytes → Bytes → Spec (Except V.VErr Unit))
    (VL : VLib) (P : PreparedNew VL) (C : TX1_345.S1Lib VL)
    (impl : TX2_213.Args → SdkState → Env → Obs (Except ProgramError Unit × SdkState))
    (root : TX1_330.RowSpec_330 L D (weaken V w) VL P C impl) :
    ∀ a s env, TX2_213.Ref L D (weaken V w) (TX1_344.asStage1 VL P C) a s env (impl a s env) :=
  fun a s env => root a s env (domain213_weaken V w VL P C a s)

/-- By contrast, the canonical instance keeps Root0 as an entry clause: the
canonical 240 domain at a 7-account state with the two admitted lengths is
exactly the Root0 statement on the entry payloads.  (This is the clause that
no program caller discharges; TCK_REPORT.md item 1.) -/
theorem domain240_canonical_is_root0 (V : V2Lib) (a : TX2_240.Args) (s : SdkState)
    (a0 a6 : AccountInfo) (h7 : a.accounts.length = 7)
    (h0 : a.accounts[0]? = some a0) (h6 : a.accounts[6]? = some a6)
    (l6 : (payload a6 s).length = CHECKPOINT_BYTES)
    (l0 : (payload a0 s).length = PROOF_ACCOUNT_BYTES)
    (dom : TX2_240.Domain V a s) :
    V.Root0 (payload a6 s) (slice (payload a0 s) AFTERSTATE_BYTES PROOF_ACCOUNT_BYTES) :=
  dom a0 a6 h7 h0 h6 l6 l0

#print axioms dom064_weaken
#print axioms domain241_weaken
#print axioms domain240_weaken
#print axioms domain213_weaken
#print axioms entry_weak_unconditional
#print axioms domain240_canonical_is_root0

end RSL.TCK
