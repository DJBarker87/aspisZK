import NDO_JGg_GammaTotal
import NDO_JGg_OrdinaryTotal
set_option autoImplicit false
namespace AspisR1.JGg_ScalarForward
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.BorrowedClaimPrepared

theorem scalar {Hash : Type} (B : PreparedModel.Boundaries) (D : aspis_core.Digest32 Hash)
    (before after : transcript.Transcript Hash) (row : U8) (payload : Slice U8)
    (block : Array U8 32#usize) (out : aspis_core.field.WideExact) (nonzero : Bool)
    (call : transcript.Transcript.block D before row payload=ok (block,after))
    (sample : (if nonzero then B.gamma block else B.ordinary block)=ok out) :
    PreparedModel.scalar B D before row payload nonzero=ok (out,after) := by
  unfold PreparedModel.scalar
  rw [call,bind_tc_ok]
  simp only [Aeneas.Std.uncurry]
  rw [sample,bind_tc_ok]
  rfl
#print axioms scalar

theorem gamma {Hash : Type} (D : aspis_core.Digest32 Hash)
    (before after : transcript.Transcript Hash) (row : U8) (payload : Slice U8)
    (block : Array U8 32#usize)
    (call : transcript.Transcript.block D before row payload=ok (block,after)) :
    ∃ out,PreparedModel.scalar closedHashBoundaries.sampling D before row payload true=ok (out,after) := by
  obtain ⟨out,sample⟩ := JGg_GammaTotal.source block
  exact ⟨out,scalar _ _ _ _ _ _ _ _ _ call sample⟩
#print axioms gamma

theorem ordinary {Hash : Type} (D : aspis_core.Digest32 Hash)
    (before after : transcript.Transcript Hash) (row : U8) (payload : Slice U8)
    (block : Array U8 32#usize)
    (call : transcript.Transcript.block D before row payload=ok (block,after)) :
    ∃ out,PreparedModel.scalar closedHashBoundaries.sampling D before row payload false=ok (out,after) := by
  obtain ⟨out,sample⟩ := JGg_OrdinaryTotal.source block
  exact ⟨out,scalar _ _ _ _ _ _ _ _ _ call sample⟩
#print axioms ordinary
end AspisR1.JGg_ScalarForward
