import NJI_PolicyParser
import NHY_ArrayExt
set_option autoImplicit false
noncomputable section
namespace NJI_PolicyCut
open Aeneas Aeneas.Std Result NJI_PolicyPort
attribute [local instance] Classical.propDecidable

/-- K009 cut, NJI_policy_cut.rs: flags and three arbitrary byte coordinates.
No successful reply, record equality or opaque-child interpretation is assumed. -/
def Coordinates (b : Slice U8) (p : P) : Prop :=
 p.flags=NHY_ZeroStep.byte b 5 ∧ ∀ i, i<32 →
 NHY_ArrayExt.coord p.registry_program i=NHY_ZeroStep.byte b (8+i) ∧
 NHY_ArrayExt.coord p.registry_authority i=NHY_ZeroStep.byte b (40+i) ∧
 NHY_ArrayExt.coord p.policy_binding i=NHY_ZeroStep.byte b (72+i)

theorem field_coordinate (b : Slice U8) (off i : Nat) (fit : off+32≤b.val.length)
 (hi : i<32) :
 NHY_ArrayExt.coord (NHY_NaturalReads.array b off 32#usize fit) i =
 NHY_ZeroStep.byte b (off+i) := by
 have hbi : off+i<b.val.length := by omega
 simp [NHY_ArrayExt.coord,NHY_NaturalReads.array,NHY_ZeroStep.byte,hi,List.getElem?_eq_getElem hbi]

theorem complete_record (b : Slice U8) (len : b.val.length=104) (p : P)
 (h : Coordinates b p) : p=NJI_PolicyParser.record b len := by
 have hp : p.registry_program=(NJI_PolicyParser.record b len).registry_program := by
  apply NHY_ArrayExt.whole
  intro i hi _
  rw [show (NJI_PolicyParser.record b len).registry_program =
    NHY_NaturalReads.array b 8 32#usize (by change 8+32≤b.val.length;omega) from rfl]
  rw [field_coordinate b 8 i _ hi]
  exact (h.2 i hi).1
 have ha : p.registry_authority=(NJI_PolicyParser.record b len).registry_authority := by
  apply NHY_ArrayExt.whole
  intro i hi _
  rw [show (NJI_PolicyParser.record b len).registry_authority =
    NHY_NaturalReads.array b 40 32#usize (by change 40+32≤b.val.length;omega) from rfl]
  rw [field_coordinate b 40 i _ hi]
  exact (h.2 i hi).2.1
 have hb : p.policy_binding=(NJI_PolicyParser.record b len).policy_binding := by
  apply NHY_ArrayExt.whole
  intro i hi _
  rw [show (NJI_PolicyParser.record b len).policy_binding =
    NHY_NaturalReads.array b 72 32#usize (by change 72+32≤b.val.length;omega) from rfl]
  rw [field_coordinate b 72 i _ hi]
  exact (h.2 i hi).2.2
 have hf : p.flags=(NJI_PolicyParser.record b len).flags := h.1
 cases p
 unfold NJI_PolicyParser.record at hp ha hb hf ⊢
 simp_all

def firstError (b : Slice U8) : Option F :=
 if b.val.take 4≠NJI_PolicyParser.magic.val then some .WrongMagic
 else if NHY_ZeroStep.byte b 4≠1#u8 then some .WrongVersion
 else if (b.val.drop 6).take 2≠List.replicate 2 0#u8 then some .NonZeroReserved
 else none

/-- Reviewed K009 transcription: exact abort firstError or entered-child coordinates,
then the unconstrained full child Err or the returned record coordinates. -/
def Cut (b : Slice U8) (reply : core.result.Result Unit F) (log : Option P)
 (out : core.result.Result P F) : Prop :=
 match firstError b with
 | some e => log=none ∧ out=.Err e
 | none => ∃ p, log=some p ∧ Coordinates b p ∧
    match reply with
    | .Err e => out=.Err e
    | .Ok _ => ∃ q, out=.Ok q ∧ Coordinates b q

def G (b : Slice U8) (len : b.val.length=104) (reply : core.result.Result Unit F) :
 core.result.Result P F :=
 match firstError b with
 | some e => .Err e
 | none => NJI_PolicyParser.validation (NJI_PolicyParser.record b len) reply

theorem cut_result (b : Slice U8) (len : b.val.length=104)
 (reply : core.result.Result Unit F) (log : Option P) (out : core.result.Result P F)
 (cut : Cut b reply log out) : out=G b len reply := by
 unfold Cut at cut
 unfold G
 cases h : firstError b with
 | some e => simp only [h] at cut ⊢;exact cut.2
 | none =>
  simp only [h] at cut ⊢
  obtain ⟨p,_,_,post⟩:=cut
  cases reply with
  | Err e => exact post
  | Ok u =>
   obtain ⟨q,same,coords⟩:=post
   rw [complete_record b len q coords] at same
   exact same

def closedReply (b : Slice U8) (len : b.val.length=104) :=
 NJI_PolicyPort.unport (NHY_PolicyModel.decode
 (NHY_PolicyModel.code (NJI_PolicyParser.record b len).flags
  (decide ((NJI_PolicyParser.record b len).registry_program=Array.repeat 32#usize 0#u8))
  (decide ((NJI_PolicyParser.record b len).registry_authority=Array.repeat 32#usize 0#u8))
  (decide ((NJI_PolicyParser.record b len).policy_binding=Array.repeat 32#usize 0#u8))))

theorem body_closed (b : Slice U8) (len : b.val.length=104) :
 NJI_PolicyParser.body b=ok (G b len (closedReply b len)) := by
 unfold NJI_PolicyParser.body G firstError closedReply
 simp only [dif_pos len,NJI_PolicyPort.validator_value,bind_tc_ok]
 by_cases hm : b.val.take 4=NJI_PolicyParser.magic.val <;>
  by_cases hv : NHY_ZeroStep.byte b 4=1#u8 <;>
  by_cases hz : (b.val.drop 6).take 2=List.replicate 2 0#u8 <;> simp_all


/-- (aq)(2): only input length and the reviewed parent cut; the CLOSED child's
complete Result is instantiated internally, never a free successful-child law. -/
theorem native_source (b : Slice U8) (len : b.val.length=104) (log : Option P)
 (out : core.result.Result P F) (cut : Cut b (closedReply b len) log out) :
 ok out=NJI_PolicyParser.raw b := by
 rw [NJI_PolicyParser.source,body_closed b len]
 exact congrArg Result.ok (cut_result b len _ log out cut)

#print native_source
#print axioms field_coordinate
#print axioms complete_record
#print axioms cut_result
#print axioms body_closed
#print axioms native_source
end NJI_PolicyCut
