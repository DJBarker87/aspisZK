import NDO_JGs_InactiveC0
import NDO_JGs_InactiveC1
import NDO_JGs_InactiveC2
import NDO_JGs_InactiveC3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_Inactive
open Aeneas Aeneas.Std Result ControlFlow
abbrev CS := core.ops.range.Range Usize × Array E 12#usize
def coefficientStates : Nat → CS
  | 0 => ({start:=0#usize,«end»:=64#usize},cs0)
  | 1 => ({start:=1#usize,«end»:=64#usize},cs1)
  | 2 => ({start:=2#usize,«end»:=64#usize},cs2)
  | 3 => ({start:=3#usize,«end»:=64#usize},cs3)
  | 4 => ({start:=4#usize,«end»:=64#usize},cs4)
  | 5 => ({start:=5#usize,«end»:=64#usize},cs5)
  | 6 => ({start:=6#usize,«end»:=64#usize},cs6)
  | 7 => ({start:=7#usize,«end»:=64#usize},cs7)
  | 8 => ({start:=8#usize,«end»:=64#usize},cs8)
  | 9 => ({start:=9#usize,«end»:=64#usize},cs9)
  | 10 => ({start:=10#usize,«end»:=64#usize},cs10)
  | 11 => ({start:=11#usize,«end»:=64#usize},cs11)
  | 12 => ({start:=12#usize,«end»:=64#usize},cs12)
  | 13 => ({start:=13#usize,«end»:=64#usize},cs13)
  | 14 => ({start:=14#usize,«end»:=64#usize},cs14)
  | 15 => ({start:=15#usize,«end»:=64#usize},cs15)
  | 16 => ({start:=16#usize,«end»:=64#usize},cs16)
  | 17 => ({start:=17#usize,«end»:=64#usize},cs17)
  | 18 => ({start:=18#usize,«end»:=64#usize},cs18)
  | 19 => ({start:=19#usize,«end»:=64#usize},cs19)
  | 20 => ({start:=20#usize,«end»:=64#usize},cs20)
  | 21 => ({start:=21#usize,«end»:=64#usize},cs21)
  | 22 => ({start:=22#usize,«end»:=64#usize},cs22)
  | 23 => ({start:=23#usize,«end»:=64#usize},cs23)
  | 24 => ({start:=24#usize,«end»:=64#usize},cs24)
  | 25 => ({start:=25#usize,«end»:=64#usize},cs25)
  | 26 => ({start:=26#usize,«end»:=64#usize},cs26)
  | 27 => ({start:=27#usize,«end»:=64#usize},cs27)
  | 28 => ({start:=28#usize,«end»:=64#usize},cs28)
  | 29 => ({start:=29#usize,«end»:=64#usize},cs29)
  | 30 => ({start:=30#usize,«end»:=64#usize},cs30)
  | 31 => ({start:=31#usize,«end»:=64#usize},cs31)
  | 32 => ({start:=32#usize,«end»:=64#usize},cs32)
  | 33 => ({start:=33#usize,«end»:=64#usize},cs33)
  | 34 => ({start:=34#usize,«end»:=64#usize},cs34)
  | 35 => ({start:=35#usize,«end»:=64#usize},cs35)
  | 36 => ({start:=36#usize,«end»:=64#usize},cs36)
  | 37 => ({start:=37#usize,«end»:=64#usize},cs37)
  | 38 => ({start:=38#usize,«end»:=64#usize},cs38)
  | 39 => ({start:=39#usize,«end»:=64#usize},cs39)
  | 40 => ({start:=40#usize,«end»:=64#usize},cs40)
  | 41 => ({start:=41#usize,«end»:=64#usize},cs41)
  | 42 => ({start:=42#usize,«end»:=64#usize},cs42)
  | 43 => ({start:=43#usize,«end»:=64#usize},cs43)
  | 44 => ({start:=44#usize,«end»:=64#usize},cs44)
  | 45 => ({start:=45#usize,«end»:=64#usize},cs45)
  | 46 => ({start:=46#usize,«end»:=64#usize},cs46)
  | 47 => ({start:=47#usize,«end»:=64#usize},cs47)
  | 48 => ({start:=48#usize,«end»:=64#usize},cs48)
  | 49 => ({start:=49#usize,«end»:=64#usize},cs49)
  | 50 => ({start:=50#usize,«end»:=64#usize},cs50)
  | 51 => ({start:=51#usize,«end»:=64#usize},cs51)
  | 52 => ({start:=52#usize,«end»:=64#usize},cs52)
  | 53 => ({start:=53#usize,«end»:=64#usize},cs53)
  | 54 => ({start:=54#usize,«end»:=64#usize},cs54)
  | 55 => ({start:=55#usize,«end»:=64#usize},cs55)
  | 56 => ({start:=56#usize,«end»:=64#usize},cs56)
  | 57 => ({start:=57#usize,«end»:=64#usize},cs57)
  | 58 => ({start:=58#usize,«end»:=64#usize},cs58)
  | 59 => ({start:=59#usize,«end»:=64#usize},cs59)
  | 60 => ({start:=60#usize,«end»:=64#usize},cs60)
  | 61 => ({start:=61#usize,«end»:=64#usize},cs61)
  | 62 => ({start:=62#usize,«end»:=64#usize},cs62)
  | 63 => ({start:=63#usize,«end»:=64#usize},cs63)
  | _ => ({start:=64#usize,«end»:=64#usize},cs64)
theorem coefficients : FIo_Native.weights.s2_grouped_inactive_pair_loop0 {start:=0#usize,«end»:=64#usize} JGq_PairShape.f
    (Array.repeat 12#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO)=ok cs64 := by
  have initial : Array.repeat 12#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=cs0 := by with_unfolding_all rfl
  rw [initial]
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0
  apply JGo_TX2_LoopChain.source
    (fun t : CS=>FIo_Native.weights.s2_grouped_inactive_pair_loop0.body JGq_PairShape.f t.1 t.2) coefficientStates 64 cs64
  · intro i hi
    interval_cases i
    · exact coefficient0
    · exact coefficient1
    · exact coefficient2
    · exact coefficient3
    · exact coefficient4
    · exact coefficient5
    · exact coefficient6
    · exact coefficient7
    · exact coefficient8
    · exact coefficient9
    · exact coefficient10
    · exact coefficient11
    · exact coefficient12
    · exact coefficient13
    · exact coefficient14
    · exact coefficient15
    · exact coefficient16
    · exact coefficient17
    · exact coefficient18
    · exact coefficient19
    · exact coefficient20
    · exact coefficient21
    · exact coefficient22
    · exact coefficient23
    · exact coefficient24
    · exact coefficient25
    · exact coefficient26
    · exact coefficient27
    · exact coefficient28
    · exact coefficient29
    · exact coefficient30
    · exact coefficient31
    · exact coefficient32
    · exact coefficient33
    · exact coefficient34
    · exact coefficient35
    · exact coefficient36
    · exact coefficient37
    · exact coefficient38
    · exact coefficient39
    · exact coefficient40
    · exact coefficient41
    · exact coefficient42
    · exact coefficient43
    · exact coefficient44
    · exact coefficient45
    · exact coefficient46
    · exact coefficient47
    · exact coefficient48
    · exact coefficient49
    · exact coefficient50
    · exact coefficient51
    · exact coefficient52
    · exact coefficient53
    · exact coefficient54
    · exact coefficient55
    · exact coefficient56
    · exact coefficient57
    · exact coefficient58
    · exact coefficient59
    · exact coefficient60
    · exact coefficient61
    · exact coefficient62
    · exact coefficient63
  · unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body
    with_unfolding_all rfl
#print axioms coefficients
end AspisR1.JGs_Inactive
end
