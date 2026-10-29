import R1Z.PV_ROWS10B_Satisfiable
set_option autoImplicit false
namespace R1Z.PV_ROWS10B_Exact64
open Aeneas Aeneas.Std PV_ROWS10B_Consumed
/-- Definitionally the carrier in ProverCommitPublicNonce40.Raw:
Fin 2 -> OracleAnswer, where OracleAnswer = Fin 32 -> UInt8.
The E1 premise below is retained T.entropy_law, not proved here. -/
abbrev Raw := Fin 2 → Fin 32 → UInt8

theorem coordinate_bound (block : Fin 2) (byte : Fin 32) :
    32 * block.val + byte.val < 64 := by omega

def decode (s : Slice U8) (length64 : s.val.length = 64) : Raw :=
  fun block byte => UInt8.ofNat
    (s.val[32 * block.val + byte.val]'(by rw [length64]; exact coordinate_bound block byte)).val

/-- Exact 64-byte request specialization, with the complete op129 carrier.
The callback equation is the unchanged E1 schema on the unchanged Raw carrier.
No syscall-fragment uniformity or independence premise occurs. -/
theorem consumed64 {E W C Word : Type} [Fintype Raw]
    (native source backend : W → Op E) (word : W → C → Word)
    (interpret : Word → Nat → Stop) (callback law : C → Raw → ℚ)
    (entry : PV_ROWS10B_Link_Entry native source)
    (body : PV_ROWS10B_Link_Body source backend)
    (control : PV_ROWS10B_Link_Control backend word interpret)
    (publicControl : PV_ROWS10B_Link_Public word)
    (coordinates : PV_ROWS10B_Link_Callback callback law)
    (entropy_law : ∀ c raw, law c raw = 1 / (Fintype.card Raw : ℚ)) :
    (∀ w s, native w s = fill (backend w) s) ∧
    (∀ a b (c : C) (sa sb : Slice U8), sa.val.length = 64 → sb.val.length = 64 →
      stop (native a sa) = stop (native b sb)) ∧
    (∀ c raw, callback c raw = 1 / (Fintype.card Raw : ℚ)) := by
  obtain ⟨full, signal, callbackLaw⟩ := consumed native source backend word interpret
    callback law entry body control publicControl coordinates entropy_law
  refine ⟨full, ?_, callbackLaw⟩
  intro a b c sa sb ha hb
  exact signal a b c sa sb (ha.trans hb.symm)

/-- Ruling (v) on the exact 64-byte Raw carrier, with the same model operation
as the preceding witness. The density is a literal explicit model density. -/
theorem exact_links_satisfiable [Fintype Raw] :
    let native := PV_ROWS10B_Satisfiable.source
    let backend := PV_ROWS10B_Satisfiable.backend
    let word := PV_ROWS10B_Satisfiable.word
    let interpret := PV_ROWS10B_Satisfiable.interpret
    let law : Unit → Raw → ℚ := fun _ _ => 1 / (Fintype.card Raw : ℚ)
    PV_ROWS10B_Link_Entry native native ∧
    PV_ROWS10B_Link_Body native backend ∧
    PV_ROWS10B_Link_Control backend word interpret ∧
    PV_ROWS10B_Link_Public word ∧
    PV_ROWS10B_Link_Callback law law ∧
    (∀ c raw, law c raw = 1 / (Fintype.card Raw : ℚ)) := by
  exact ⟨PV_ROWS10B_Satisfiable.all_links.1,
    PV_ROWS10B_Satisfiable.all_links.2.1,
    PV_ROWS10B_Satisfiable.all_links.2.2.1,
    PV_ROWS10B_Satisfiable.all_links.2.2.2.1, rfl, fun _ _ => rfl⟩
#print axioms coordinate_bound
#print axioms consumed64
#print axioms exact_links_satisfiable
end R1Z.PV_ROWS10B_Exact64
