import XRz_ParseFold
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSc_ParseCuts
def tail27 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 r181 r191 r201 r211 r221 r231 r241 r251 r261 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let i1 :=
   Slice.len bytes
 if offset != i1
 then
   ok
     (core.result.Result.Err
     r1_wire.Error.TrailingBytes)
 else
   ok
     (core.result.Result.Ok
     {
       c1_root :=
         root,
       records :=
         (Array.make
         27#usize [
         r0, r11,
         r21, r31,
         r41, r51,
         r61, r71,
         r81, r91,
         r101, r111,
         r121, r131,
         r141, r151,
         r161, r171,
         r181, r191,
         r201, r211,
         r221, r231,
         r241, r251,
         r261
         ])
     })

def tail26 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 r181 r191 r201 r211 r221 r231 r241 r251 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r29 ←
   r1_wire.parse_record_at
     bytes 26#u8
     offset
 let cf26 ←
   core.result.Result.Insts.CoreOpsTry.branch
     r29
 match cf26 with
 |
   core.ops.control_flow.ControlFlow.Continue
   p26 =>
   let (r261,
     offset26) :=
     p26
   tail27 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 r181 r191 r201 r211 r221 r231 r241 r251 r261 offset26
 |
   core.ops.control_flow.ControlFlow.Break
   residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix
     (core.convert.FromSame
     r1_wire.Error)
     residual

def tail25 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 r181 r191 r201 r211 r221 r231 r241 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r28 ←
   r1_wire.parse_record_at
     bytes 25#u8
     offset
 let cf25 ←
   core.result.Result.Insts.CoreOpsTry.branch
     r28
 match cf25 with
 |
   core.ops.control_flow.ControlFlow.Continue
   p25 =>
   let (r251, offset25)
     :=
     p25
   tail26 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 r181 r191 r201 r211 r221 r231 r241 r251 offset25
 |
   core.ops.control_flow.ControlFlow.Break
   residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix
     (core.convert.FromSame
     r1_wire.Error)
     residual

def tail24 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 r181 r191 r201 r211 r221 r231 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r27 ←
   r1_wire.parse_record_at
     bytes 24#u8 offset
 let cf24 ←
   core.result.Result.Insts.CoreOpsTry.branch
     r27
 match cf24 with
 |
   core.ops.control_flow.ControlFlow.Continue
   p24 =>
   let (r241, offset24) :=
     p24
   tail25 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 r181 r191 r201 r211 r221 r231 r241 offset24
 |
   core.ops.control_flow.ControlFlow.Break
   residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix
     (core.convert.FromSame
     r1_wire.Error)
     residual

def tail23 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 r181 r191 r201 r211 r221 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r26 ←
   r1_wire.parse_record_at
     bytes 23#u8 offset
 let cf23 ←
   core.result.Result.Insts.CoreOpsTry.branch
     r26
 match cf23 with
 |
   core.ops.control_flow.ControlFlow.Continue
   p23 =>
   let (r231, offset23) :=
     p23
   tail24 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 r181 r191 r201 r211 r221 r231 offset23
 |
   core.ops.control_flow.ControlFlow.Break
   residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix
     (core.convert.FromSame
     r1_wire.Error) residual

def tail22 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 r181 r191 r201 r211 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r25 ←
   r1_wire.parse_record_at
     bytes 22#u8 offset
 let cf22 ←
   core.result.Result.Insts.CoreOpsTry.branch
     r25
 match cf22 with
 |
   core.ops.control_flow.ControlFlow.Continue
   p22 =>
   let (r221, offset22) := p22
   tail23 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 r181 r191 r201 r211 r221 offset22
 |
   core.ops.control_flow.ControlFlow.Break
   residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix
     (core.convert.FromSame
     r1_wire.Error) residual

def tail21 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 r181 r191 r201 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r24 ←
   r1_wire.parse_record_at bytes
     21#u8 offset
 let cf21 ←
   core.result.Result.Insts.CoreOpsTry.branch
     r24
 match cf21 with
 |
   core.ops.control_flow.ControlFlow.Continue
   p21 =>
   let (r211, offset21) := p21
   tail22 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 r181 r191 r201 r211 offset21
 |
   core.ops.control_flow.ControlFlow.Break
   residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix
     (core.convert.FromSame
     r1_wire.Error) residual

def tail20 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 r181 r191 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r23 ←
   r1_wire.parse_record_at bytes
     20#u8 offset
 let cf20 ←
   core.result.Result.Insts.CoreOpsTry.branch
     r23
 match cf20 with
 |
   core.ops.control_flow.ControlFlow.Continue
   p20 =>
   let (r201, offset20) := p20
   tail21 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 r181 r191 r201 offset20
 |
   core.ops.control_flow.ControlFlow.Break
   residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix
     (core.convert.FromSame
     r1_wire.Error) residual

def tail19 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 r181 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r22 ←
   r1_wire.parse_record_at bytes
     19#u8 offset
 let cf19 ←
   core.result.Result.Insts.CoreOpsTry.branch
     r22
 match cf19 with
 |
   core.ops.control_flow.ControlFlow.Continue
   p19 =>
   let (r191, offset19) := p19
   tail20 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 r181 r191 offset19
 |
   core.ops.control_flow.ControlFlow.Break
   residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix
     (core.convert.FromSame
     r1_wire.Error) residual

def tail18 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r20 ←
   r1_wire.parse_record_at bytes 18#u8
     offset
 let cf18 ←
   core.result.Result.Insts.CoreOpsTry.branch
     r20
 match cf18 with
 |
   core.ops.control_flow.ControlFlow.Continue
   p18 =>
   let (r181, offset18) := p18
   tail19 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 r181 offset18
 |
   core.ops.control_flow.ControlFlow.Break
   residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix
     (core.convert.FromSame
     r1_wire.Error) residual

def tail17 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r19 ←
   r1_wire.parse_record_at bytes 17#u8
     offset
 let cf17 ←
   core.result.Result.Insts.CoreOpsTry.branch
     r19
 match cf17 with
 |
   core.ops.control_flow.ControlFlow.Continue
   p17 =>
   let (r171, offset17) := p17
   tail18 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 r171 offset17
 |
   core.ops.control_flow.ControlFlow.Break
   residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix
     (core.convert.FromSame
     r1_wire.Error) residual

def tail16 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r18 ←
   r1_wire.parse_record_at bytes 16#u8
     offset
 let cf16 ←
   core.result.Result.Insts.CoreOpsTry.branch
     r18
 match cf16 with
 |
   core.ops.control_flow.ControlFlow.Continue
   p16 =>
   let (r161, offset16) := p16
   tail17 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 r161 offset16
 | core.ops.control_flow.ControlFlow.Break
   residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix (core.convert.FromSame
     r1_wire.Error) residual

def tail15 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r17 ←
   r1_wire.parse_record_at bytes 15#u8
     offset
 let cf15 ←
   core.result.Result.Insts.CoreOpsTry.branch
     r17
 match cf15 with
 |
   core.ops.control_flow.ControlFlow.Continue
   p15 =>
   let (r151, offset15) := p15
   tail16 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 r151 offset15
 | core.ops.control_flow.ControlFlow.Break
   residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix (core.convert.FromSame
     r1_wire.Error) residual

def tail14 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r16 ←
   r1_wire.parse_record_at bytes 14#u8
     offset
 let cf14 ←
   core.result.Result.Insts.CoreOpsTry.branch
     r16
 match cf14 with
 | core.ops.control_flow.ControlFlow.Continue
   p14 =>
   let (r141, offset14) := p14
   tail15 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 r141 offset14
 | core.ops.control_flow.ControlFlow.Break
   residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix (core.convert.FromSame
     r1_wire.Error) residual

def tail13 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r15 ←
   r1_wire.parse_record_at bytes 13#u8 offset
 let cf13 ←
   core.result.Result.Insts.CoreOpsTry.branch
     r15
 match cf13 with
 | core.ops.control_flow.ControlFlow.Continue
   p13 =>
   let (r131, offset13) := p13
   tail14 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 r131 offset13
 | core.ops.control_flow.ControlFlow.Break
   residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix (core.convert.FromSame
     r1_wire.Error) residual

def tail12 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r14 ←
   r1_wire.parse_record_at bytes 12#u8 offset
 let cf12 ←
   core.result.Result.Insts.CoreOpsTry.branch r14
 match cf12 with
 | core.ops.control_flow.ControlFlow.Continue p12
   =>
   let (r121, offset12) := p12
   tail13 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 r121 offset12
 | core.ops.control_flow.ControlFlow.Break
   residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix (core.convert.FromSame
     r1_wire.Error) residual

def tail11 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r13 ←
   r1_wire.parse_record_at bytes 11#u8 offset
 let cf11 ←
   core.result.Result.Insts.CoreOpsTry.branch r13
 match cf11 with
 | core.ops.control_flow.ControlFlow.Continue p11 =>
   let (r111, offset11) := p11
   tail12 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 r111 offset11
 | core.ops.control_flow.ControlFlow.Break residual
   =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix (core.convert.FromSame
     r1_wire.Error) residual

def tail10 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r12 ←
   r1_wire.parse_record_at bytes 10#u8 offset
 let cf10 ←
   core.result.Result.Insts.CoreOpsTry.branch r12
 match cf10 with
 | core.ops.control_flow.ControlFlow.Continue p10 =>
   let (r101, offset10) := p10
   tail11 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 r101 offset10
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix (core.convert.FromSame
     r1_wire.Error) residual

def tail9 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 r81 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r10 ← r1_wire.parse_record_at bytes 9#u8 offset
 let cf9 ←
   core.result.Result.Insts.CoreOpsTry.branch r10
 match cf9 with
 | core.ops.control_flow.ControlFlow.Continue p9 =>
   let (r91, offset9) := p9
   tail10 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 r91 offset9
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix (core.convert.FromSame
     r1_wire.Error) residual

def tail8 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 r71 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r9 ← r1_wire.parse_record_at bytes 8#u8 offset
 let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r9
 match cf8 with
 | core.ops.control_flow.ControlFlow.Continue p8 =>
   let (r81, offset8) := p8
   tail9 bytes root r0 r11 r21 r31 r41 r51 r61 r71 r81 offset8
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix (core.convert.FromSame r1_wire.Error)
     residual

def tail7 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 r61 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r8 ← r1_wire.parse_record_at bytes 7#u8 offset
 let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r8
 match cf7 with
 | core.ops.control_flow.ControlFlow.Continue p7 =>
   let (r71, offset7) := p7
   tail8 bytes root r0 r11 r21 r31 r41 r51 r61 r71 offset7
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix (core.convert.FromSame r1_wire.Error)
     residual

def tail6 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 r51 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r7 ← r1_wire.parse_record_at bytes 6#u8 offset
 let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r7
 match cf6 with
 | core.ops.control_flow.ControlFlow.Continue p6 =>
   let (r61, offset6) := p6
   tail7 bytes root r0 r11 r21 r31 r41 r51 r61 offset6
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix (core.convert.FromSame r1_wire.Error)
     residual

def tail5 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 r41 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r6 ← r1_wire.parse_record_at bytes 5#u8 offset
 let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r6
 match cf5 with
 | core.ops.control_flow.ControlFlow.Continue p5 =>
   let (r51, offset5) := p5
   tail6 bytes root r0 r11 r21 r31 r41 r51 offset5
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix (core.convert.FromSame r1_wire.Error)
     residual

def tail4 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 r31 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r5 ← r1_wire.parse_record_at bytes 4#u8 offset
 let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
 match cf4 with
 | core.ops.control_flow.ControlFlow.Continue p4 =>
   let (r41, offset4) := p4
   tail5 bytes root r0 r11 r21 r31 r41 offset4
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix (core.convert.FromSame r1_wire.Error) residual

def tail3 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 r21 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r4 ← r1_wire.parse_record_at bytes 3#u8 offset
 let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r4
 match cf3 with
 | core.ops.control_flow.ControlFlow.Continue p3 =>
   let (r31, offset3) := p3
   tail4 bytes root r0 r11 r21 r31 offset3
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix (core.convert.FromSame r1_wire.Error) residual

def tail2 (bytes : Slice U8) (root : Array U8 32#usize) (r0 r11 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r3 ← r1_wire.parse_record_at bytes 2#u8 offset
 let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r3
 match cf2 with
 | core.ops.control_flow.ControlFlow.Continue p2 =>
   let (r21, offset2) := p2
   tail3 bytes root r0 r11 r21 offset2
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix (core.convert.FromSame r1_wire.Error) residual

def tail1 (bytes : Slice U8) (root : Array U8 32#usize) (r0 : Slice U8) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r2 ← r1_wire.parse_record_at bytes 1#u8 offset
 let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
 match cf1 with
 | core.ops.control_flow.ControlFlow.Continue p1 =>
   let (r11, offset1) := p1
   tail2 bytes root r0 r11 offset1
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix (core.convert.FromSame r1_wire.Error) residual

def tail0 (bytes : Slice U8) (root : Array U8 32#usize) (offset : Usize) : Result (core.result.Result r1_wire.Prefix r1_wire.Error) := do
 let r1 ← r1_wire.parse_record_at bytes 0#u8 offset
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
 match cf with
 | core.ops.control_flow.ControlFlow.Continue p =>
   let (r0, offset) := p
   tail1 bytes root r0 offset
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     r1_wire.Prefix (core.convert.FromSame r1_wire.Error) residual
end XSc_ParseCuts
