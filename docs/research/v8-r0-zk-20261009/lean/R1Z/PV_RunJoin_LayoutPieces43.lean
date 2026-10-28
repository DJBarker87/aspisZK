import R1Z.PV_RunJoin_CanonicalRecord43
import R1Z.PV_RunJoin_RoundStream43
import R1Z.PV_RunJoin_LayoutDomain41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LayoutPieces43
open Aeneas Aeneas.Std ProverRwFull PV_RunJoin_CanonicalRecord43 PV_RunJoin_RoundStream43
variable [ExternalTypes]
theorem domain (ops : ExternalFuns) (logical : Slice U8)
    (prefix masked rounded claimed : List U8) (prefix_length : prefix.length=134)
    (mask : Piece 32 prefix masked) (rounds : Stream masked 10 rounded)
    (claim : Piece 3712 rounded claimed) (endpoint : Piece 928 claimed logical.val) :
    ∃ records, PV_RunJoin_SemanticDomain40.Domain ops logical 27#u8 32#usize 0#u8 records := by
  have ml : masked.length=171 := by have h := PV_RunJoin_CanonicalRecord43.length mask;omega
  have rl : rounded.length=9181 := by have h := PV_RunJoin_RoundStream43.length rounds;omega
  have cl : claimed.length=12898 := by have h := PV_RunJoin_CanonicalRecord43.length claim;omega
  have fl : logical.length=13831 := by
    have h := PV_RunJoin_CanonicalRecord43.length endpoint
    change logical.val.length=13831
    omega
  have et := PV_RunJoin_CanonicalRecord43.extension endpoint
  have ct := PV_RunJoin_ByteExtension43.trans (PV_RunJoin_CanonicalRecord43.extension claim) et
  have rt := PV_RunJoin_ByteExtension43.trans (PV_RunJoin_RoundStream43.extension rounds) ct
  have hm := PV_RunJoin_CanonicalRecord43.slot mask rt
  rw [prefix_length] at hm
  have hr : ∀ k, k<10 → PV_RunJoin_HighDomain40.HighZero
      ((logical.val.drop (176+901*k)).take 896) := by
    intro k hk
    have h := PV_RunJoin_RoundStream43.canonical rounds k hk
    rw [ml] at h
    have bound : (171+901*k+5)+896≤rounded.length := by rw [rl];omega
    have hfinal := PV_RunJoin_CanonicalRecord43.preserve ct bound h
    have off : 176+901*k=171+901*k+5 := by omega
    rw [off]
    exact hfinal
  have hc := PV_RunJoin_CanonicalRecord43.slot claim et
  rw [rl] at hc
  have he := PV_RunJoin_CanonicalRecord43.slot endpoint
    (PV_RunJoin_ByteExtension43.refl logical.val)
  rw [cl] at he
  exact PV_RunJoin_LayoutDomain41.domain ops logical fl hm
    (hr 0 (by omega)) (hr 1 (by omega)) (hr 2 (by omega)) (hr 3 (by omega)) (hr 4 (by omega)) (hr 5 (by omega)) (hr 6 (by omega)) (hr 7 (by omega)) (hr 8 (by omega)) (hr 9 (by omega)) hc he
#print axioms domain
end R1Z.PV_RunJoin_LayoutPieces43
