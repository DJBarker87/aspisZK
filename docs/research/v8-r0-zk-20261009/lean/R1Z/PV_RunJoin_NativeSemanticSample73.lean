import R1Z.PV_RunJoin_NativeSamplerTotal73
import R1Z.PV_RunJoin_SemanticDigest51
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeSemanticSample73
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63
abbrev T := host_wire.SemanticTranscript aspis_core.digest.LegacyHashFn
variable {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)

theorem digest (hash : aspis_core.digest.LegacyHashFn) (parts : Slice (Slice U8)) :
    @ExternalFuns.op39 (types base) (opsNative base heap box ops runtime world) hash parts=hash parts := by
  unfold opsNative PV_RunJoin_WeightInstalled46.selected
  rw [PV_B2_F_RawNative.preserved_39]
  rfl

#print axioms digest

theorem validated (t : T) (row : U8) (framed : Slice U8) (order : row=t.next_row)
    (total : ∀ parts,∃ b,t.hash parts=ok b) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    ∃ block advanced, host_wire.SemanticTranscript.sample_block_validated
      aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 t row framed=
      ok (.Ok block,{t with state:=advanced,next_row:=U8.wrapping_add row 1#u8}) := by
  subst row
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  obtain ⟨absorbed,ha⟩ := total (PV_RunJoin_SemanticRequests51.request t.state t.next_row framed)
  obtain ⟨block,hb⟩ := total (PV_RunJoin_TranscriptRequests51.message absorbed 1#u8)
  obtain ⟨advanced,hc⟩ := total (PV_RunJoin_TranscriptRequests51.message absorbed 2#u8)
  refine ⟨block,advanced,?_⟩
  rw [PV_RunJoin_SemanticRequests51.source]
  simp only [aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32,
    aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32.digest,
    digest base heap box ops runtime world]
  simp only [bne_self_eq_false,Bool.false_eq_true,if_false,ha,hb,hc,bind_tc_ok]

theorem complete (t : T) (row : U8) (framed payload : Slice U8) (order : row=t.next_row)
    (bound : row.val ≤ 24) (total : ∀ parts,∃ b,t.hash parts=ok b)
    (parsed : @host_wire.parse_record (types base) (opsNative base heap box ops runtime world)
      row framed=ok (.Ok payload)) :
    letI : ExternalTypes := types base
    letI : ExternalFuns := opsNative base heap box ops runtime world
    ∃ q next, host_wire.SemanticTranscript.semantic
      aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32 t row framed=ok (.Ok q,next) ∧
      next.next_row=U8.wrapping_add row 1#u8 ∧ next.hash=t.hash := by
  subst row
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  obtain ⟨block,advanced,hv⟩ := validated base heap box ops runtime world t t.next_row framed rfl total
  obtain ⟨q,hq⟩ := PV_RunJoin_NativeSamplerTotal73.complete base heap box ops runtime world block
  refine ⟨q,{t with state:=advanced,next_row:=U8.wrapping_add t.next_row 1#u8},?_,rfl,rfl⟩
  have lower : ¬t.next_row>24#u8 := Nat.not_lt.mpr bound
  simp only [host_wire.SemanticTranscript.semantic,lower,if_false,
    host_wire.SemanticTranscript.sample_block,bne_self_eq_false,Bool.false_eq_true,
    parsed,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,hv,hq,Aeneas.Std.uncurry]

#print axioms validated
#print axioms complete
end R1Z.PV_RunJoin_NativeSemanticSample73
