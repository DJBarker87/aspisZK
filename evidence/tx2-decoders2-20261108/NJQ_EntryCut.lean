import NJQ_Entry
import NJI_PolicyCut
set_option autoImplicit false
noncomputable section
namespace NJQ_EntryCut
open Aeneas Aeneas.Std Result NJI_V1Carrier
attribute [local instance] Classical.propDecidable

def statusReply (x : U8) : core.result.Result S F :=
 match x with
 | 0#uscalar => .Ok .Pending
 | 1#uscalar => .Ok .Active
 | 2#uscalar => .Ok .Paused
 | 3#uscalar => .Ok .Retired
 | _ => .Err .InvalidStatus

def statusValue (x : U8) : S :=
 match statusReply x with | .Ok s=>s | .Err _=>.Retired

theorem status_source (x : U8) :
 NJI_Extracted.aspis_statement.pool_v1.verifier_registry.VerifierEntryStatusV1.Insts.CoreConvertTryFromU8PoolV1VerifierRegistryFormatError.try_from x=ok (statusReply x) := by
 unfold NJI_Extracted.aspis_statement.pool_v1.verifier_registry.VerifierEntryStatusV1.Insts.CoreConvertTryFromU8PoolV1VerifierRegistryFormatError.try_from statusReply
 split <;> first | rfl | (split <;> simp_all)

abbrev record (b : Slice U8) (len : b.val.length=192) :=
 NJQ_Entry.record b len (statusValue (NHY_ZeroStep.byte b 5))

def Coordinates (b : Slice U8) (len : b.val.length=192) (p : E) : Prop :=
 p.status=statusValue (NHY_ZeroStep.byte b 5) ∧
 p.statement_version=NHY_ZeroStep.byte b 6 ∧ p.bump=NHY_ZeroStep.byte b 7 ∧
 p.activation_slot=core.num.U64.from_le_bytes (NHY_NaturalReads.array b 136 8#usize (by change 136+8≤b.val.length;omega)) ∧
 p.retirement_slot=core.num.U64.from_le_bytes (NHY_NaturalReads.array b 144 8#usize (by change 144+8≤b.val.length;omega)) ∧
 ∀ i,i<32 →
 NHY_ArrayExt.coord p.pool i=NHY_ZeroStep.byte b (8+i) ∧
 NHY_ArrayExt.coord p.verifier_program i=NHY_ZeroStep.byte b (40+i) ∧
 NHY_ArrayExt.coord p.profile_binding i=NHY_ZeroStep.byte b (72+i) ∧
 NHY_ArrayExt.coord p.release_binding i=NHY_ZeroStep.byte b (104+i) ∧
 NHY_ArrayExt.coord p.policy_binding i=NHY_ZeroStep.byte b (152+i)

theorem complete_record (b : Slice U8) (len : b.val.length=192) (p : E)
 (h : Coordinates b len p) : p=record b len := by
 have h_pool : p.pool=(record b len).pool := by
  apply NHY_ArrayExt.whole
  intro i hi _
  rw [show (record b len).pool=
   NHY_NaturalReads.array b 8 32#usize (by change 8+32≤b.val.length;omega) from rfl]
  rw [NJI_PolicyCut.field_coordinate b 8 i _ hi]
  exact (h.2.2.2.2.2 i hi).1
 have h_verifier_program : p.verifier_program=(record b len).verifier_program := by
  apply NHY_ArrayExt.whole
  intro i hi _
  rw [show (record b len).verifier_program=
   NHY_NaturalReads.array b 40 32#usize (by change 40+32≤b.val.length;omega) from rfl]
  rw [NJI_PolicyCut.field_coordinate b 40 i _ hi]
  exact (h.2.2.2.2.2 i hi).2.1
 have h_profile_binding : p.profile_binding=(record b len).profile_binding := by
  apply NHY_ArrayExt.whole
  intro i hi _
  rw [show (record b len).profile_binding=
   NHY_NaturalReads.array b 72 32#usize (by change 72+32≤b.val.length;omega) from rfl]
  rw [NJI_PolicyCut.field_coordinate b 72 i _ hi]
  exact (h.2.2.2.2.2 i hi).2.2.1
 have h_release_binding : p.release_binding=(record b len).release_binding := by
  apply NHY_ArrayExt.whole
  intro i hi _
  rw [show (record b len).release_binding=
   NHY_NaturalReads.array b 104 32#usize (by change 104+32≤b.val.length;omega) from rfl]
  rw [NJI_PolicyCut.field_coordinate b 104 i _ hi]
  exact (h.2.2.2.2.2 i hi).2.2.2.1
 have h_policy_binding : p.policy_binding=(record b len).policy_binding := by
  apply NHY_ArrayExt.whole
  intro i hi _
  rw [show (record b len).policy_binding=
   NHY_NaturalReads.array b 152 32#usize (by change 152+32≤b.val.length;omega) from rfl]
  rw [NJI_PolicyCut.field_coordinate b 152 i _ hi]
  exact (h.2.2.2.2.2 i hi).2.2.2.2
 have hs:=h.1
 have hv:=h.2.1
 have hb:=h.2.2.1
 have ha:=h.2.2.2.1
 have hr:=h.2.2.2.2.1
 cases p
 unfold record NJQ_Entry.record at *
 simp_all

def firstError (b : Slice U8) : Option F :=
 if b.val.take 4≠NJQ_Entry.magic.val then some .WrongMagic
 else if NHY_ZeroStep.byte b 4≠2#u8 then some .WrongVersion
 else if (b.val.drop 184).take 8≠List.replicate 8 0#u8 then some .NonZeroReserved
 else match statusReply (NHY_ZeroStep.byte b 5) with | .Err e=>some e | .Ok _=>none

/-- K027/K028: no child log after any prefix rejection (including invalid status),
otherwise the exact input record and full reply/error are retained. -/
def Cut (b : Slice U8) (len : b.val.length=192) (reply : core.result.Result Unit F)
 (log : Option E) (out : core.result.Result E F) : Prop :=
 match firstError b with
 | some e => log=none ∧ out=.Err e
 | none => ∃ p,log=some p ∧ Coordinates b len p ∧
   match reply with
   | .Err e=>out=.Err e
   | .Ok _=>∃ q,out=.Ok q ∧ Coordinates b len q

def G (b : Slice U8) (len : b.val.length=192) (reply : core.result.Result Unit F) : core.result.Result E F :=
 match firstError b with
 | some e=>.Err e
 | none=>match reply with | .Err e=>.Err e | .Ok _=>.Ok (record b len)

theorem cut_result (b : Slice U8) (len : b.val.length=192) (reply : core.result.Result Unit F)
 (log : Option E) (out : core.result.Result E F) (cut : Cut b len reply log out) : out=G b len reply := by
 unfold Cut at cut
 unfold G
 cases he : firstError b with
 | some e=>simp only [he] at cut ⊢;exact cut.2
 | none=>
   simp only [he] at cut ⊢
   obtain ⟨_,_,_,post⟩:=cut
   cases reply with
   | Err e=>exact post
   | Ok u=>
     obtain ⟨q,same,coords⟩:=post
     rw [complete_record b len q coords] at same
     exact same

def reply (r : E) : core.result.Result Unit F :=
 if r.statement_version=0#u8 then .Err .InvalidStatementVersion
 else if NJI_V1Models.Z r.pool then .Err .ZeroRequiredBinding
 else if NJI_V1Models.Z r.verifier_program then .Err .ZeroRequiredBinding
 else if NJI_V1Models.Z r.profile_binding then .Err .ZeroRequiredBinding
 else if NJI_V1Models.Z r.release_binding then .Err .ZeroRequiredBinding
 else if NJI_V1Models.Z r.policy_binding then .Err .ZeroRequiredBinding
 else if r.retirement_slot=18446744073709551615#u64 then .Ok ()
 else if r.retirement_slot≤r.activation_slot then .Err .InvalidRetirementSlot
 else .Ok ()

theorem child (r : E) : NJI_V1Models.entry r=ok (reply r) := by
 dsimp only [NJI_V1Models.entry,reply]
 split <;> try simp_all
 all_goals first | rfl | (split <;> try simp_all)
 all_goals first | rfl | (split <;> try simp_all)
 all_goals first | rfl | (split <;> try simp_all)
 all_goals first | rfl | (split <;> try simp_all)
 all_goals first | rfl | (split <;> try simp_all)
 all_goals first | rfl | (split <;> try simp_all)
 all_goals first | rfl | (split <;> try simp_all)

def closedReply (b : Slice U8) (len : b.val.length=192) := reply (record b len)

theorem body_closed (b : Slice U8) (len : b.val.length=192) :
 NJQ_Entry.model b=ok (G b len (closedReply b len)) := by
 unfold NJQ_Entry.model G firstError
 simp only [dif_pos len,status_source,bind_tc_ok]
 by_cases hm : b.val.take 4=NJQ_Entry.magic.val <;>
  by_cases hv : NHY_ZeroStep.byte b 4=2#u8 <;>
  by_cases hz : (b.val.drop 184).take 8=List.replicate 8 0#u8 <;> simp_all
 all_goals
  cases hs : statusReply (NHY_ZeroStep.byte b 5) with
  | Err e=>simp only [hs,bind_tc_ok]
  | Ok status=>
    simp only [hs,bind_tc_ok]
    have same : record b len=NJQ_Entry.record b len status := by simp only [record,statusValue,hs]
    simp only [←same,child,bind_tc_ok,closedReply]
    cases reply (record b len) <;> rfl

theorem native_source (b : Slice U8) (len : b.val.length=192) (log : Option E)
 (out : core.result.Result E F) (cut : Cut b len (closedReply b len) log out) :
 ok out=NJQ_Entry.reference b := by
 rw [NJQ_Entry.source,body_closed b len]
 exact congrArg Result.ok (cut_result b len _ log out cut)

#print native_source
#print axioms status_source
#print axioms complete_record
#print axioms cut_result
#print axioms child
#print axioms body_closed
#print axioms native_source
end NJQ_EntryCut
