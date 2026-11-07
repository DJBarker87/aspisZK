import LIB_VDecodeTotal
import LIB_VRecords
set_option autoImplicit false
noncomputable section
namespace LIB_VDecode
open Aeneas Aeneas.Std LIB_VCarriers
open LIB_VScalarCarriers (RawQ array toRaw)
open AspisR1PublicPreparation.RawActualDecodeKMainAdapter
def liftResult {N : Usize} : (out : core.result.Result (Array RawQ N) WErr) →
 LIB_VDecodeTotal.Good out → Except WErr (Array QM31 N)
 | .Ok a,h => .ok (LIB_VArray.lift a h)
 | .Err e,_ => .error e
theorem liftResult_raw {N : Usize} (out : core.result.Result (Array RawQ N) WErr)
 (h : LIB_VDecodeTotal.Good out) :
 LIB_VRecords.raw ((liftResult out h).map (array toRaw)) = out := by
 cases out with
 | Err e => rfl
 | Ok a =>
  change core.result.Result.Ok (array toRaw (LIB_VArray.lift a h)) = .Ok a
  rw [LIB_VArray.raw_lift]
def offset (n : Nat) : Usize := Usize.ofNat (n%4294967296) (by scalar_tac)
theorem offset_value (n : Nat) (h : n≤116) : (offset n).val=n := by
 change n%4294967296=n
 exact Nat.mod_eq_of_lt (by omega)
/-- Exact TX1:147 supported call shapes and frame geometry from NGO, verbatim. -/
def Domain (r : Record) (n : Nat) : Prop :=
 NGO_CallerDomains.Call r.row.val (29#usize).val n ∧
 r.framed.val.length=5+NFU_PacketDomains.payloadSize r.row.val
theorem total (r : Record) (n : Nat) (h : Domain r n) :
 ∃ out,decodeMain 29#usize r (offset n)=.ok out ∧ LIB_VDecodeTotal.Good out := by
 have bounds := NGO_CallerDomains.numeric r.row.val 29 n h.1
 have hn : n≤116 := by omega
 exact LIB_VDecodeTotal.total 29#usize (offset n) r
  (by simpa only [offset_value n hn] using h.1) h.2
/-- Outside the CLOSED own-input domain no native credit is claimed.
The domain branch never assumes a decoder result or child success. -/
def decodeK29 (r : Record) (n : Nat) : Except WErr K29 := by
 classical
 exact if h : Domain r n then liftResult (Classical.choose (total r n h))
  (Classical.choose_spec (total r n h)).2
 else .error .InvalidRow
theorem decode_exact (r : Record) (n : Nat) (h : Domain r n) :
 decodeMain 29#usize r (offset n) =
 .ok (LIB_VRecords.raw ((decodeK29 r n).map k29Raw)) := by
 classical
 simp only [decodeK29,dif_pos h]
 unfold k29Raw
 rw [liftResult_raw]
 exact (Classical.choose_spec (total r n h)).1
#print axioms liftResult_raw
#print axioms offset_value
#print axioms total
#print axioms decode_exact
end LIB_VDecode
