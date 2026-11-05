import NGU_Part006
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGY_Decoder
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_LPm_RawPort
open AspisR1CurrentPreparedClaim

def scalar (b : Slice U8) : NQ :=
 ⟨⟨NGU_LPq_BytesTotal.word b 0,NGU_LPq_BytesTotal.word b 1⟩,
   ⟨NGU_LPq_BytesTotal.word b 2,NGU_LPq_BytesTotal.word b 3⟩⟩

theorem limbs (a : Array U32 8#usize) (out : NE)
 (run : FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs a=ok (some out)) :
 out.c0=⟨⟨a.val[0],a.val[1]⟩,⟨a.val[2],a.val[3]⟩⟩ := by
 have r0 := NGU_ArrayRead.read a 0#usize (by decide)
 have r1 := NGU_ArrayRead.read a 1#usize (by decide)
 have r2 := NGU_ArrayRead.read a 2#usize (by decide)
 have r3 := NGU_ArrayRead.read a 3#usize (by decide)
 have r4 := NGU_ArrayRead.read a 4#usize (by decide)
 have r5 := NGU_ArrayRead.read a 5#usize (by decide)
 have r6 := NGU_ArrayRead.read a 6#usize (by decide)
 have r7 := NGU_ArrayRead.read a 7#usize (by decide)
 simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs,r0,r1,r2,r3,r4,r5,r6,r7,bind_tc_ok] at run
 repeat' first | split at run | cases run
 all_goals rfl

theorem bytes (b : Slice U8) (len : b.val.length=32) (out : NE)
 (run : FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes b=ok (some out)) :
 out.c0=scalar b := by
 have hlen : Slice.len b=32#usize := by
  apply UScalar.eq_of_val_eq
  change b.val.length=_
  rw [len]
  rfl
 have r0 := NGU_LPq_BytesTotal.read b len 0#usize (by decide)
 have r1 := NGU_LPq_BytesTotal.read b len 1#usize (by decide)
 have r2 := NGU_LPq_BytesTotal.read b len 2#usize (by decide)
 have r3 := NGU_LPq_BytesTotal.read b len 3#usize (by decide)
 have r4 := NGU_LPq_BytesTotal.read b len 4#usize (by decide)
 have r5 := NGU_LPq_BytesTotal.read b len 5#usize (by decide)
 have r6 := NGU_LPq_BytesTotal.read b len 6#usize (by decide)
 have r7 := NGU_LPq_BytesTotal.read b len 7#usize (by decide)
 have r8 := NGU_LPq_BytesTotal.read b len 8#usize (by decide)
 have r9 := NGU_LPq_BytesTotal.read b len 9#usize (by decide)
 have r10 := NGU_LPq_BytesTotal.read b len 10#usize (by decide)
 have r11 := NGU_LPq_BytesTotal.read b len 11#usize (by decide)
 have r12 := NGU_LPq_BytesTotal.read b len 12#usize (by decide)
 have r13 := NGU_LPq_BytesTotal.read b len 13#usize (by decide)
 have r14 := NGU_LPq_BytesTotal.read b len 14#usize (by decide)
 have r15 := NGU_LPq_BytesTotal.read b len 15#usize (by decide)
 have r16 := NGU_LPq_BytesTotal.read b len 16#usize (by decide)
 have r17 := NGU_LPq_BytesTotal.read b len 17#usize (by decide)
 have r18 := NGU_LPq_BytesTotal.read b len 18#usize (by decide)
 have r19 := NGU_LPq_BytesTotal.read b len 19#usize (by decide)
 have r20 := NGU_LPq_BytesTotal.read b len 20#usize (by decide)
 have r21 := NGU_LPq_BytesTotal.read b len 21#usize (by decide)
 have r22 := NGU_LPq_BytesTotal.read b len 22#usize (by decide)
 have r23 := NGU_LPq_BytesTotal.read b len 23#usize (by decide)
 have r24 := NGU_LPq_BytesTotal.read b len 24#usize (by decide)
 have r25 := NGU_LPq_BytesTotal.read b len 25#usize (by decide)
 have r26 := NGU_LPq_BytesTotal.read b len 26#usize (by decide)
 have r27 := NGU_LPq_BytesTotal.read b len 27#usize (by decide)
 have r28 := NGU_LPq_BytesTotal.read b len 28#usize (by decide)
 have r29 := NGU_LPq_BytesTotal.read b len 29#usize (by decide)
 have r30 := NGU_LPq_BytesTotal.read b len 30#usize (by decide)
 have r31 := NGU_LPq_BytesTotal.read b len 31#usize (by decide)
 simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes,FIo_Native.aspis_core.field.wide_exact.WideExact.BYTE_LEN,hlen,bne_self_eq_false,↓reduceIte,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,bind_tc_ok,lift] at run
 have value := limbs _ out run
 simpa only [scalar,NGU_LPq_BytesTotal.word,NGU_LPq_BytesTotal.byte,Array.make,List.getElem!_cons_zero,List.getElem!_cons_succ,List.getElem_cons_zero,List.getElem_cons_succ,UScalar.ofNatCore_val_eq] using value

theorem selected {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
 (hy : NGU_LPq_SelectedDomain.ByteDomain y1) (lane : Usize) (hl : lane.val<29)
 (point : Usize) (hp : point.val=5) :
 ∃ b, NGU_LPq_SelectedDomain.selected y1 lane=ok b ∧ b.val.length=32 ∧
  canonQ (scalar b) ∧
  ClaimScalar.read NGU_LPm_PointLoop.ops sem y1 point lane=ok (qPort (scalar b)) := by
 obtain ⟨b,window,len,words⟩ := hy lane hl
 obtain ⟨out,decode,canonical⟩ := NGU_LPq_BytesTotal.source b len words
 have projection := bytes b len out decode
 have field : FIo_Native.weights.field y1 lane=ok out := by
  change (do let b ← NGU_LPq_SelectedDomain.selected y1 lane
             let o ← FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes b
             core.option.Option.unwrap o)=_
  rw [window,bind_tc_ok,decode,bind_tc_ok]
  rfl
 have port := NGU_LPq_Decoder.claim_field y1 lane hl
 rw [field] at port
 have hlarge : ¬ point≤2#usize := by scalar_tac
 refine ⟨b,window,len,?_,?_⟩
 · rw [←projection]
   exact canonical.1
 · simp only [ClaimScalar.read,if_neg hlarge,hp]
   change (do let e ← ClaimParser.field y1 lane; ClaimParser.c0 e)=_
   rw [←port]
   change ok (qPort out.c0)=ok (qPort (scalar b))
   rw [projection]

#print axioms limbs
#print axioms bytes
#print axioms selected
end AspisR1.NGY_Decoder
end
