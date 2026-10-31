import NEC_HeaderMagic
import NEC_HeaderBinding0
import NEC_HeaderBinding1
import NEC_HeaderBinding2
import NEC_HeaderBinding3
import NEC_HeaderMonad
set_option autoImplicit false
namespace NEC_HeaderJoin
open Aeneas Aeneas.Std Result NEC_HeaderPredicates

def code (length : Usize) (a : Array U8 48#usize) : U8 :=
 if length != 800#usize then 1#u8 else
 if magic a then
  if byte a 8#usize (by decide) != 1#u8 then 3#u8 else
  if byte a 9#usize (by decide) != 0#u8 then 4#u8 else
  if byte a 10#usize (by decide) != 0#u8 then 4#u8 else
  if byte a 11#usize (by decide) != 0#u8 then 4#u8 else
  if byte a 12#usize (by decide) != 0#u8 then 4#u8 else
  if byte a 13#usize (by decide) != 0#u8 then 4#u8 else
  if byte a 14#usize (by decide) != 0#u8 then 4#u8 else
  if byte a 15#usize (by decide) != 0#u8 then 4#u8 else
  if binding0 a then
   if binding1 a then
    if binding2 a then
     if binding3 a then 0#u8 else 5#u8
    else 5#u8
   else 5#u8
  else 5#u8
 else 2#u8

theorem emitted (length : Usize) (a : Array U8 48#usize) :
 NEC_LiveHeaderRef.live_header_ref length a=ok (code length a) := by
 have h8 : Array.index_usize a 8#usize=ok (byte a 8#usize (by decide)) := byte_spec a _ (by decide)
 have h9 : Array.index_usize a 9#usize=ok (byte a 9#usize (by decide)) := byte_spec a _ (by decide)
 have h10 : Array.index_usize a 10#usize=ok (byte a 10#usize (by decide)) := byte_spec a _ (by decide)
 have h11 : Array.index_usize a 11#usize=ok (byte a 11#usize (by decide)) := byte_spec a _ (by decide)
 have h12 : Array.index_usize a 12#usize=ok (byte a 12#usize (by decide)) := byte_spec a _ (by decide)
 have h13 : Array.index_usize a 13#usize=ok (byte a 13#usize (by decide)) := byte_spec a _ (by decide)
 have h14 : Array.index_usize a 14#usize=ok (byte a 14#usize (by decide)) := byte_spec a _ (by decide)
 have h15 : Array.index_usize a 15#usize=ok (byte a 15#usize (by decide)) := byte_spec a _ (by decide)
 simp only [NEC_LiveHeaderRef.live_header_ref,code,NEC_HeaderMagic.emitted,NEC_HeaderBinding0.emitted,NEC_HeaderBinding1.emitted,NEC_HeaderBinding2.emitted,NEC_HeaderBinding3.emitted,h8,h9,h10,h11,h12,h13,h14,h15,bind_tc_ok,NEC_HeaderMonad.ok_if]

#print axioms emitted
end NEC_HeaderJoin
