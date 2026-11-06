import NJQ_Registry
import NJI_PolicyCut
set_option autoImplicit false
noncomputable section
namespace NJQ_RegistryCut
open Aeneas Aeneas.Std Result NJI_V1Carrier
attribute [local instance] Classical.propDecidable
abbrev word (b : Slice U8) (off : Nat) (fit : off+8≤b.val.length) :=
 core.num.U64.from_le_bytes (NHY_NaturalReads.array b off 8#usize fit)

def Coordinates (b : Slice U8) (len : b.val.length=128) (p : R) : Prop :=
 p.flags=NHY_ZeroStep.byte b 5 ∧ p.bump=NHY_ZeroStep.byte b 6 ∧
 p.generation=word b 104 (by omega) ∧ p.minimum_activation_delay_slots=word b 112 (by omega) ∧
 ∀ i,i<32 →
 NHY_ArrayExt.coord p.pool i=NHY_ZeroStep.byte b (8+i) ∧
 NHY_ArrayExt.coord p.authority i=NHY_ZeroStep.byte b (40+i) ∧
 NHY_ArrayExt.coord p.policy_binding i=NHY_ZeroStep.byte b (72+i)

theorem complete_record (b : Slice U8) (len : b.val.length=128) (p : R)
 (h : Coordinates b len p) : p=NJQ_Registry.record b len := by
 have h_pool : p.pool=(NJQ_Registry.record b len).pool := by
  apply NHY_ArrayExt.whole
  intro i hi _
  rw [show (NJQ_Registry.record b len).pool=
   NHY_NaturalReads.array b 8 32#usize (by change 8+32≤b.val.length;omega) from rfl]
  rw [NJI_PolicyCut.field_coordinate b 8 i _ hi]
  exact (h.2.2.2.2 i hi).1
 have h_authority : p.authority=(NJQ_Registry.record b len).authority := by
  apply NHY_ArrayExt.whole
  intro i hi _
  rw [show (NJQ_Registry.record b len).authority=
   NHY_NaturalReads.array b 40 32#usize (by change 40+32≤b.val.length;omega) from rfl]
  rw [NJI_PolicyCut.field_coordinate b 40 i _ hi]
  exact (h.2.2.2.2 i hi).2.1
 have h_policy_binding : p.policy_binding=(NJQ_Registry.record b len).policy_binding := by
  apply NHY_ArrayExt.whole
  intro i hi _
  rw [show (NJQ_Registry.record b len).policy_binding=
   NHY_NaturalReads.array b 72 32#usize (by change 72+32≤b.val.length;omega) from rfl]
  rw [NJI_PolicyCut.field_coordinate b 72 i _ hi]
  exact (h.2.2.2.2 i hi).2.2
 have hf := h.1
 have hb := h.2.1
 have hg := h.2.2.1
 have hd := h.2.2.2.1
 cases p
 unfold NJQ_Registry.record at *
 simp_all

def firstError (b : Slice U8) : Option F :=
 if b.val.take 4≠NJQ_Registry.magic.val then some .WrongMagic
 else if NHY_ZeroStep.byte b 4≠2#u8 then some .WrongVersion
 else if NHY_ZeroStep.byte b 7≠0#u8 ∨ (b.val.drop 120).take 8≠List.replicate 8 0#u8 then some .NonZeroReserved
 else none

/-- Exact K029/K030 clauses: full early error, child arguments by coordinates,
full child Err, and returning coordinates; no accepted-child or endpoint premise. -/
def Cut (b : Slice U8) (len : b.val.length=128) (reply : core.result.Result Unit F)
 (log : Option R) (out : core.result.Result R F) : Prop :=
 match firstError b with
 | some e => log=none ∧ out=.Err e
 | none => ∃ p,log=some p ∧ Coordinates b len p ∧
   match reply with
   | .Err e => out=.Err e
   | .Ok _ => ∃ q,out=.Ok q ∧ Coordinates b len q

def G (b : Slice U8) (len : b.val.length=128) (reply : core.result.Result Unit F) : core.result.Result R F :=
 match firstError b with
 | some e => .Err e
 | none => match reply with | .Ok _=>.Ok (NJQ_Registry.record b len) | .Err e=>.Err e

theorem cut_result (b : Slice U8) (len : b.val.length=128) (reply : core.result.Result Unit F)
 (log : Option R) (out : core.result.Result R F) (cut : Cut b len reply log out) : out=G b len reply := by
 unfold Cut at cut
 unfold G
 cases he : firstError b with
 | some e => simp only [he] at cut ⊢;exact cut.2
 | none =>
   simp only [he] at cut ⊢
   obtain ⟨_,_,_,post⟩:=cut
   cases reply with
   | Err e => exact post
   | Ok u =>
     obtain ⟨q,same,coords⟩:=post
     rw [complete_record b len q coords] at same
     exact same

/-- CLOSED child has a total full-Result model, internally instantiated. -/
def closedReply (b : Slice U8) (len : b.val.length=128) : core.result.Result Unit F :=
 let r := NJQ_Registry.record b len
 if r.flags &&& (~~~ 3#u8) != 0#u8 then .Err .UnsupportedFlags
 else if NJI_V1Models.Z r.pool then .Err .ZeroRequiredBinding
 else if NJI_V1Models.Z r.policy_binding then .Err .ZeroRequiredBinding
 else if (r.flags &&& 2#u8 != 0#u8) != NJI_V1Models.Z r.authority then .Err .InvalidAuthorityMode
 else if r.minimum_activation_delay_slots=0#u64 then .Err .InvalidActivationDelay
 else .Ok ()

theorem child (b : Slice U8) (len : b.val.length=128) :
 NJI_V1Models.registry (NJQ_Registry.record b len)=ok (closedReply b len) := by
 dsimp only [NJI_V1Models.registry,closedReply]
 split <;> try simp_all
 all_goals first | rfl | (split <;> try simp_all)
 all_goals first | rfl | (split <;> try simp_all)
 all_goals first | rfl | (split <;> try simp_all)
 all_goals first | rfl | (split <;> try simp_all)

theorem body_closed (b : Slice U8) (len : b.val.length=128) :
 NJQ_Registry.model b=ok (G b len (closedReply b len)) := by
 unfold NJQ_Registry.model G firstError
 simp only [dif_pos len,child,bind_tc_ok]
 by_cases hm : b.val.take 4=NJQ_Registry.magic.val <;>
  by_cases hv : NHY_ZeroStep.byte b 4=2#u8 <;>
  by_cases h7 : NHY_ZeroStep.byte b 7=0#u8 <;>
  by_cases hz : (b.val.drop 120).take 8=List.replicate 8 0#u8 <;> simp_all
 all_goals cases closedReply b len <;> rfl

theorem native_source (b : Slice U8) (len : b.val.length=128) (log : Option R)
 (out : core.result.Result R F) (cut : Cut b len (closedReply b len) log out) :
 ok out=NJQ_Registry.reference b := by
 rw [NJQ_Registry.source,body_closed b len]
 exact congrArg Result.ok (cut_result b len _ log out cut)

#print native_source
#print axioms complete_record
#print axioms cut_result
#print axioms child
#print axioms body_closed
#print axioms native_source
end NJQ_RegistryCut
