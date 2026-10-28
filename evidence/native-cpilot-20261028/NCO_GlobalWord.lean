import NCO_Address
import NCO_WordNat
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_GlobalWord

def word (payload : Slice U8) (i j : Nat) : U32 :=
  NCO_Word.packed (NCO_Address.byte payload (32*i+4*j))
    (NCO_Address.byte payload (32*i+4*j+1))
    (NCO_Address.byte payload (32*i+4*j+2))
    (NCO_Address.byte payload (32*i+4*j+3))

def Good (payload : Slice U8) (i j : Nat) : Prop :=
  word payload i j < 2147483647#u32 ∧ (j < 4 ∨ word payload i j = 0#u32)

theorem step (payload : Slice U8) (i j : Usize)
    (cap : payload.val.length ≤ 3712) (hi : i.val < payload.val.length / 32) (hj : j.val < 8) :
    ∃ successor : Usize, successor.val = j.val+1 ∧
      NCO_ParserRef.validate_ref_loop0_loop0.body payload i j =
        if word payload i.val j.val >= 2147483647#u32 then ok (.done (i,0#u32))
        else if j >= 4#usize then
          if word payload i.val j.val != 0#u32 then ok (.done (i,0#u32))
          else ok (.cont successor)
        else ok (.cont successor) := by
  have geom := NCO_Address.geometry payload.val.length i.val j.val cap hi hj
  obtain ⟨p⟩ := NCO_Address.arithmetic i j geom.1 hj
  have r0 : Slice.index_usize payload p.at1 =
      ok (NCO_Address.byte payload (32*i.val+4*j.val)) := by
    simpa only [p.at_val] using NCO_Address.read payload p.at1 (by rw [p.at_val]; omega)
  have r1 : Slice.index_usize payload p.a1 =
      ok (NCO_Address.byte payload (32*i.val+4*j.val+1)) := by
    simpa only [p.a1_val,p.at_val] using NCO_Address.read payload p.a1 (by rw [p.a1_val,p.at_val]; omega)
  have r2 : Slice.index_usize payload p.a2 =
      ok (NCO_Address.byte payload (32*i.val+4*j.val+2)) := by
    simpa only [p.a2_val,p.at_val] using NCO_Address.read payload p.a2 (by rw [p.a2_val,p.at_val]; omega)
  have r3 : Slice.index_usize payload p.a3 =
      ok (NCO_Address.byte payload (32*i.val+4*j.val+3)) := by
    simpa only [p.a3_val,p.at_val] using NCO_Address.read payload p.a3 (by rw [p.a3_val,p.at_val]; omega)
  exact ⟨p.successor,p.successor_val,NCO_WordStep.step payload i j p.p p.q p.at1 p.a1 p.a2 p.a3 p.successor
    _ _ _ _ hj p.mul0 p.mul1 p.add p.add1 p.add2 p.add3 p.increment r0 r1 r2 r3⟩

#print axioms step
end NCO_GlobalWord
