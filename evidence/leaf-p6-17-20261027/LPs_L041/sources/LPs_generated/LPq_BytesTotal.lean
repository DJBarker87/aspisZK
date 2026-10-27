import LPq_DecodeTotal
set_option autoImplicit false
namespace AspisR1.LPq_BytesTotal
open Aeneas Aeneas.Std Result LPi_FieldValues

def byte (b : Slice U8) (i : Nat) : U8 := b.val[i]?.getD 0#u8
def word (b : Slice U8) (j : Nat) : U32 := core.num.U32.from_le_bytes
  (Array.make 4#usize [byte b (4*j),byte b (4*j+1),byte b (4*j+2),byte b (4*j+3)])

theorem read (b : Slice U8) (len : b.val.length=32) (i : Usize) (hi : i.val<32) :
    Slice.index_usize b i=ok (byte b i.val) := by
  obtain ⟨v,run,value⟩ := WP.spec_imp_exists (Slice.index_usize_spec b i (by simpa only [Slice.length,len] using hi))
  rw [value] at run
  simpa only [byte,List.getElem?_eq_getElem (show i.val<b.val.length by omega),Option.getD_some] using run

theorem source (b : Slice U8) (len : b.val.length=32)
    (hc : ∀ j, j<8 → (word b j).val<2147483647) :
    ∃ out, FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes b=ok (some out) ∧ canonE out := by
  let a : Array U32 8#usize := Array.make 8#usize [word b 0,word b 1,word b 2,word b 3,word b 4,word b 5,word b 6,word b 7]
  have ca : ∀ i, ∀ h : i<a.val.length, (a.val[i]'h).val<2147483647 := by
    intro i hi
    have bound : i<8 := by simpa only [a,Array.make,List.length_cons,List.length_nil] using hi
    interval_cases i
    · exact hc 0 (by decide)
    · exact hc 1 (by decide)
    · exact hc 2 (by decide)
    · exact hc 3 (by decide)
    · exact hc 4 (by decide)
    · exact hc 5 (by decide)
    · exact hc 6 (by decide)
    · exact hc 7 (by decide)
  obtain ⟨out,call,co⟩ := LPq_DecodeTotal.limbs a ca
  have hlen : Slice.len b=32#usize := by
    apply UScalar.eq_of_val_eq
    change b.val.length=_
    rw [len]
    rfl
  refine ⟨out,?_,co⟩
  simp only [FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes,
    FIo_Native.aspis_core.field.wide_exact.WideExact.BYTE_LEN,hlen,bne_self_eq_false,↓reduceIte]
  have r0 := read b len 0#usize (by decide)
  have r1 := read b len 1#usize (by decide)
  have r2 := read b len 2#usize (by decide)
  have r3 := read b len 3#usize (by decide)
  have r4 := read b len 4#usize (by decide)
  have r5 := read b len 5#usize (by decide)
  have r6 := read b len 6#usize (by decide)
  have r7 := read b len 7#usize (by decide)
  have r8 := read b len 8#usize (by decide)
  have r9 := read b len 9#usize (by decide)
  have r10 := read b len 10#usize (by decide)
  have r11 := read b len 11#usize (by decide)
  have r12 := read b len 12#usize (by decide)
  have r13 := read b len 13#usize (by decide)
  have r14 := read b len 14#usize (by decide)
  have r15 := read b len 15#usize (by decide)
  have r16 := read b len 16#usize (by decide)
  have r17 := read b len 17#usize (by decide)
  have r18 := read b len 18#usize (by decide)
  have r19 := read b len 19#usize (by decide)
  have r20 := read b len 20#usize (by decide)
  have r21 := read b len 21#usize (by decide)
  have r22 := read b len 22#usize (by decide)
  have r23 := read b len 23#usize (by decide)
  have r24 := read b len 24#usize (by decide)
  have r25 := read b len 25#usize (by decide)
  have r26 := read b len 26#usize (by decide)
  have r27 := read b len 27#usize (by decide)
  have r28 := read b len 28#usize (by decide)
  have r29 := read b len 29#usize (by decide)
  have r30 := read b len 30#usize (by decide)
  have r31 := read b len 31#usize (by decide)
  simpa only [r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,UScalar.ofNatCore_val_eq,bind_tc_ok,lift,word,byte,a,Bool.false_eq_true,if_false] using call

#print axioms read
#print axioms source
end AspisR1.LPq_BytesTotal
