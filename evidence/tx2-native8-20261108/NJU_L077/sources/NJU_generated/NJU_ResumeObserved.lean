import NJU_Log
import NJR_ReservationSites
set_option autoImplicit false
noncomputable section
namespace NJU_ResumeObserved
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
abbrev K := aspis_core.field.QM31
abbrev E := aspis_core.field.wide_exact.WideExact
abbrev R (A : Type) := Result (core.result.Result A verifier.Error)

/-- Full replies at actual entered resume sites. This is a source-log stage;
its native cut association must still be assembled and is not a root premise. -/
inductive Event where
 | digest (chunks : Slice (Slice U8)) (reply : Result (Array U8 32#usize))
 | headerAny (it : core.slice.iter.Iter U8) (reply : Result (Bool × core.slice.iter.Iter U8))
 | raw (n : Usize) (reader : verifier.Reader) (reply : Result (Array U8 n × verifier.Reader))
 | k (reader : verifier.Reader) (reply : Result (core.result.Result K verifier.Error × verifier.Reader))
 | e (reader : verifier.Reader) (reply : Result (core.result.Result E verifier.Error × verifier.Reader))
 | semantic (bytes : Slice U8) (cursor : Usize) (reply : R (Array K 10#usize × Usize))
 | weights (bytes : Slice U8) (cursor : Usize) (before : alloc.vec.Vec K)
   (reply : R (alloc.vec.Vec K × Usize))
 | validate (queries : Array U32 22#usize) (reply : R Unit)
 | filled (n : Usize) (value : K)
   (reply : Result (core.result.Result (alloc.vec.Vec K) aspis_core.r0.Error))

def recordRaw (n : Usize) (reader : verifier.Reader) : NJU_Log.Run Event (Array U8 n × verifier.Reader) :=
 NJU_Log.record (.raw n reader) (NJC_ConcreteUnwrap.raw n reader)
def recordK (reader : verifier.Reader) : NJU_Log.Run Event (core.result.Result K verifier.Error × verifier.Reader) :=
 NJU_Log.record (.k reader) (NIL_FreshOps.readK reader)
def recordE (reader : verifier.Reader) : NJU_Log.Run Event (core.result.Result E verifier.Error × verifier.Reader) :=
 NJU_Log.record (.e reader) (NIL_FreshOps.readE reader)
def recordSemantic (bytes : Slice U8) (cursor : Usize) : NJU_Log.Run Event (core.result.Result (Array K 10#usize × Usize) verifier.Error) :=
 NJU_Log.record (.semantic bytes cursor) (NIL_FreshOps.semantic bytes cursor)
def recordWeights (bytes : Slice U8) (cursor : Usize) (weights : alloc.vec.Vec K) : NJU_Log.Run Event (core.result.Result (alloc.vec.Vec K × Usize) verifier.Error) :=
 NJU_Log.record (.weights bytes cursor weights) (NIL_FreshOps.weights bytes cursor weights)
def recordValidate (queries : Array U32 22#usize) : NJU_Log.Run Event (core.result.Result Unit verifier.Error) :=
 NJU_Log.record (.validate queries) (NJC_ValidateEmission.verifier.validate_checkpoint_queries queries)
def recordFilled (r : NP6_StdModel.Reservation) (copy : core.marker.Copy K) (n : Usize) (value : K) :
 NJU_Log.Run Event (core.result.Result (alloc.vec.Vec K) aspis_core.r0.Error) :=
 NJU_Log.record (.filled n value) (NIL_FreshOps.filled (NJC_FilledClause.reserved r) copy n value)
def recordAny {F : Type} (inst : core.ops.function.FnMut F U8 Bool) (it : core.slice.iter.Iter U8) (f : F) :
 NJU_Log.Run Event (Bool × core.slice.iter.Iter U8) :=
 NJU_Log.record (.headerAny it) (NIL_FreshOps.any inst it f)
def recordDigest {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H) (chunks : Slice (Slice U8)) :
 NJU_Log.Run Event (Array U8 32#usize) :=
 NJU_Log.record (.digest chunks) ((NIL_FreshOps.digest d).digest hash chunks)

def finishTailG (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K)
 (queryValues : Array U32 22#usize) (r34 : verifier.Reader) : NJU_Log.Run Event (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
 let r36 ←
   recordSemantic bytes
     r34.«at»
 let cf6 ←
   core.result.Result.Insts.CoreOpsTry.branch
     r36
 match cf6 with
 | core.ops.control_flow.ControlFlow.Continue
   val5 =>
   let (semantic_alpha, at1) := val5
   let (r37, r38) ←
     recordK
       { r34 with «at» := at1 }
   let cf7 ←
     core.result.Result.Insts.CoreOpsTry.branch
       r37
   match cf7 with
   | core.ops.control_flow.ControlFlow.Continue
     val6 =>
     let (r39, r40) ← recordK r38
     let cf8 ←
       core.result.Result.Insts.CoreOpsTry.branch
         r39
     match cf8 with
     |
       core.ops.control_flow.ControlFlow.Continue
       val7 =>
       let (r41, r42) ← recordK r40
       let cf9 ←
         core.result.Result.Insts.CoreOpsTry.branch
           r41
       match cf9 with
       |
         core.ops.control_flow.ControlFlow.Continue
         val8 =>
         let (r43, r44) ←
           recordK r42
         let cf10 ←
           core.result.Result.Insts.CoreOpsTry.branch
             r43
         match cf10 with
         |
           core.ops.control_flow.ControlFlow.Continue
           val9 =>
           let (r45, r46) ←
             recordE r44
           let cf11 ←
             core.result.Result.Insts.CoreOpsTry.branch
               r45
           match cf11 with
           |
             core.ops.control_flow.ControlFlow.Continue
             val10 =>
             let (r47, r48) ←
               recordE r46
             let cf12 ←
               core.result.Result.Insts.CoreOpsTry.branch
                 r47
             match cf12 with
             |
               core.ops.control_flow.ControlFlow.Continue
               val11 =>
               let (r49, r50) ←
                 recordK r48
               let cf13 ←
                 core.result.Result.Insts.CoreOpsTry.branch
                   r49
               match cf13 with
               |
                 core.ops.control_flow.ControlFlow.Continue
                 val12 =>
                 let i30 ←
                   (fun v=>CheckpointBytes4Ops.finalLen (NIL_Carriers.variant v)) v
                 let q ←
                   (ok (NIL_Carriers.unK ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩))
                 let r51 ←
                   (recordFilled reservation)
                     (aspis_core.field.QM31.Insts.CoreMarkerCopy (fun x=>ok x))
                     i30 q
                 let r52 ←
                   NIL_FreshOps.mapError
                     (verifier.resume.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError
                     (NIL_FreshOps.digest d))
                     r51 ()
                 let cf14 ←
                   core.result.Result.Insts.CoreOpsTry.branch
                     r52
                 match cf14 with
                 |
                   core.ops.control_flow.ControlFlow.Continue
                   val13 =>
                   let r53 ←
                     recordWeights
                       bytes r50.«at» val13
                   let cf15 ←
                     core.result.Result.Insts.CoreOpsTry.branch
                       r53
                   match cf15 with
                   |
                     core.ops.control_flow.ControlFlow.Continue
                     val14 =>
                     let (weights, at2) := val14
                     if at2 != end1
                     then
                       ok
                         (core.result.Result.Err
                         verifier.Error.Checkpoint)
                     else
                       let i31 ←
                         lift (UScalar.cast
                           .Usize i4)
                       ok (core.result.Result.Ok
                         ({
                            variant := v,
                            roots :=
                              (Array.make
                                 2#usize [
                                a3, a4
                                ]),
                            gamma := val,
                            kappa := val1,
                            alpha :=
                              (Array.make
                                 2#usize [
                                val2, val3
                                ]),
                            rho := val4,
                            queries :=
                              queryValues,
                            semantic_alpha,
                            z :=
                              (Array.make
                                 2#usize [
                                {
                                  x := val6,
                                  y := val7
                                },
                                {
                                  x := val8,
                                  y := val9
                                }
                                ]),
                            claim := val10,
                            state
                          },
                         {
                           weights,
                           rhs := val11,
                           power := val12,
                           next := i31
                         }))
                   |
                     core.ops.control_flow.ControlFlow.Break
                     residual =>
                     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                       (verifier.Prepared ×
                       verifier.Accumulator)
                       (core.convert.FromSame
                       verifier.Error) residual
                 |
                   core.ops.control_flow.ControlFlow.Break
                   residual =>
                   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                     (verifier.Prepared ×
                     verifier.Accumulator)
                     (core.convert.FromSame
                     verifier.Error) residual
               |
                 core.ops.control_flow.ControlFlow.Break
                 residual =>
                 core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                   (verifier.Prepared ×
                   verifier.Accumulator)
                   (core.convert.FromSame
                   verifier.Error) residual
             |
               core.ops.control_flow.ControlFlow.Break
               residual =>
               core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                 (verifier.Prepared ×
                 verifier.Accumulator)
                 (core.convert.FromSame
                 verifier.Error) residual
           |
             core.ops.control_flow.ControlFlow.Break
             residual =>
             core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
               (verifier.Prepared ×
               verifier.Accumulator)
               (core.convert.FromSame
               verifier.Error) residual
         |
           core.ops.control_flow.ControlFlow.Break
           residual =>
           core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
             (verifier.Prepared ×
             verifier.Accumulator)
             (core.convert.FromSame
             verifier.Error) residual
       | core.ops.control_flow.ControlFlow.Break
         residual =>
         core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
           (verifier.Prepared ×
           verifier.Accumulator)
           (core.convert.FromSame
           verifier.Error) residual
     | core.ops.control_flow.ControlFlow.Break
       residual =>
       core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
         (verifier.Prepared ×
         verifier.Accumulator)
         (core.convert.FromSame verifier.Error)
         residual
   | core.ops.control_flow.ControlFlow.Break
     residual =>
     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
       (verifier.Prepared ×
       verifier.Accumulator)
       (core.convert.FromSame verifier.Error)
       residual
 | core.ops.control_flow.ControlFlow.Break
   residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     (verifier.Prepared × verifier.Accumulator)
     (core.convert.FromSame verifier.Error)
     residual

def finishTailR (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K)
 (queryValues : Array U32 22#usize) (r34 : verifier.Reader) : Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
 let r36 ←
   NIL_FreshOps.semantic bytes
     r34.«at»
 let cf6 ←
   core.result.Result.Insts.CoreOpsTry.branch
     r36
 match cf6 with
 | core.ops.control_flow.ControlFlow.Continue
   val5 =>
   let (semantic_alpha, at1) := val5
   let (r37, r38) ←
     NIL_FreshOps.readK
       { r34 with «at» := at1 }
   let cf7 ←
     core.result.Result.Insts.CoreOpsTry.branch
       r37
   match cf7 with
   | core.ops.control_flow.ControlFlow.Continue
     val6 =>
     let (r39, r40) ← NIL_FreshOps.readK r38
     let cf8 ←
       core.result.Result.Insts.CoreOpsTry.branch
         r39
     match cf8 with
     |
       core.ops.control_flow.ControlFlow.Continue
       val7 =>
       let (r41, r42) ← NIL_FreshOps.readK r40
       let cf9 ←
         core.result.Result.Insts.CoreOpsTry.branch
           r41
       match cf9 with
       |
         core.ops.control_flow.ControlFlow.Continue
         val8 =>
         let (r43, r44) ←
           NIL_FreshOps.readK r42
         let cf10 ←
           core.result.Result.Insts.CoreOpsTry.branch
             r43
         match cf10 with
         |
           core.ops.control_flow.ControlFlow.Continue
           val9 =>
           let (r45, r46) ←
             NIL_FreshOps.readE r44
           let cf11 ←
             core.result.Result.Insts.CoreOpsTry.branch
               r45
           match cf11 with
           |
             core.ops.control_flow.ControlFlow.Continue
             val10 =>
             let (r47, r48) ←
               NIL_FreshOps.readE r46
             let cf12 ←
               core.result.Result.Insts.CoreOpsTry.branch
                 r47
             match cf12 with
             |
               core.ops.control_flow.ControlFlow.Continue
               val11 =>
               let (r49, r50) ←
                 NIL_FreshOps.readK r48
               let cf13 ←
                 core.result.Result.Insts.CoreOpsTry.branch
                   r49
               match cf13 with
               |
                 core.ops.control_flow.ControlFlow.Continue
                 val12 =>
                 let i30 ←
                   (fun v=>CheckpointBytes4Ops.finalLen (NIL_Carriers.variant v)) v
                 let q ←
                   (ok (NIL_Carriers.unK ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩))
                 let r51 ←
                   (NIL_FreshOps.filled (NJC_FilledClause.reserved reservation))
                     (aspis_core.field.QM31.Insts.CoreMarkerCopy (fun x=>ok x))
                     i30 q
                 let r52 ←
                   NIL_FreshOps.mapError
                     (verifier.resume.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError
                     (NIL_FreshOps.digest d))
                     r51 ()
                 let cf14 ←
                   core.result.Result.Insts.CoreOpsTry.branch
                     r52
                 match cf14 with
                 |
                   core.ops.control_flow.ControlFlow.Continue
                   val13 =>
                   let r53 ←
                     NIL_FreshOps.weights
                       bytes r50.«at» val13
                   let cf15 ←
                     core.result.Result.Insts.CoreOpsTry.branch
                       r53
                   match cf15 with
                   |
                     core.ops.control_flow.ControlFlow.Continue
                     val14 =>
                     let (weights, at2) := val14
                     if at2 != end1
                     then
                       ok
                         (core.result.Result.Err
                         verifier.Error.Checkpoint)
                     else
                       let i31 ←
                         lift (UScalar.cast
                           .Usize i4)
                       ok (core.result.Result.Ok
                         ({
                            variant := v,
                            roots :=
                              (Array.make
                                 2#usize [
                                a3, a4
                                ]),
                            gamma := val,
                            kappa := val1,
                            alpha :=
                              (Array.make
                                 2#usize [
                                val2, val3
                                ]),
                            rho := val4,
                            queries :=
                              queryValues,
                            semantic_alpha,
                            z :=
                              (Array.make
                                 2#usize [
                                {
                                  x := val6,
                                  y := val7
                                },
                                {
                                  x := val8,
                                  y := val9
                                }
                                ]),
                            claim := val10,
                            state
                          },
                         {
                           weights,
                           rhs := val11,
                           power := val12,
                           next := i31
                         }))
                   |
                     core.ops.control_flow.ControlFlow.Break
                     residual =>
                     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                       (verifier.Prepared ×
                       verifier.Accumulator)
                       (core.convert.FromSame
                       verifier.Error) residual
                 |
                   core.ops.control_flow.ControlFlow.Break
                   residual =>
                   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                     (verifier.Prepared ×
                     verifier.Accumulator)
                     (core.convert.FromSame
                     verifier.Error) residual
               |
                 core.ops.control_flow.ControlFlow.Break
                 residual =>
                 core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                   (verifier.Prepared ×
                   verifier.Accumulator)
                   (core.convert.FromSame
                   verifier.Error) residual
             |
               core.ops.control_flow.ControlFlow.Break
               residual =>
               core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                 (verifier.Prepared ×
                 verifier.Accumulator)
                 (core.convert.FromSame
                 verifier.Error) residual
           |
             core.ops.control_flow.ControlFlow.Break
             residual =>
             core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
               (verifier.Prepared ×
               verifier.Accumulator)
               (core.convert.FromSame
               verifier.Error) residual
         |
           core.ops.control_flow.ControlFlow.Break
           residual =>
           core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
             (verifier.Prepared ×
             verifier.Accumulator)
             (core.convert.FromSame
             verifier.Error) residual
       | core.ops.control_flow.ControlFlow.Break
         residual =>
         core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
           (verifier.Prepared ×
           verifier.Accumulator)
           (core.convert.FromSame
           verifier.Error) residual
     | core.ops.control_flow.ControlFlow.Break
       residual =>
       core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
         (verifier.Prepared ×
         verifier.Accumulator)
         (core.convert.FromSame verifier.Error)
         residual
   | core.ops.control_flow.ControlFlow.Break
     residual =>
     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
       (verifier.Prepared ×
       verifier.Accumulator)
       (core.convert.FromSame verifier.Error)
       residual
 | core.ops.control_flow.ControlFlow.Break
   residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     (verifier.Prepared × verifier.Accumulator)
     (core.convert.FromSame verifier.Error)
     residual

def queryEndG (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K)
 (i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 : U32) (r28 : verifier.Reader) : NJU_Log.Run Event (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
 let (a21, r29) ←
   recordRaw 4#usize r28
 let i24 ← lift (core.num.U32.from_le_bytes a21)
 let (a22, r30) ←
   recordRaw 4#usize r29
 let i25 ← lift (core.num.U32.from_le_bytes a22)
 let (a23, r31) ←
   recordRaw 4#usize r30
 let i26 ← lift (core.num.U32.from_le_bytes a23)
 let (a24, r32) ←
   recordRaw 4#usize r31
 let i27 ← lift (core.num.U32.from_le_bytes a24)
 let (a25, r33) ←
   recordRaw 4#usize r32
 let i28 ← lift (core.num.U32.from_le_bytes a25)
 let (a26, r34) ←
   recordRaw 4#usize r33
 let i29 ← lift (core.num.U32.from_le_bytes a26)
 let queryValues := (Array.make 22#usize [
       i8, i9, i10, i11, i12, i13, i14, i15, i16,
       i17, i18, i19, i20, i21, i22, i23, i24,
       i25, i26, i27, i28, i29
       ])
 let r35 ←
   recordValidate
     queryValues
 let cf5 ←
   core.result.Result.Insts.CoreOpsTry.branch r35
 match cf5 with
 | core.ops.control_flow.ControlFlow.Continue _ =>
   finishTailG reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 queryValues r34
 | core.ops.control_flow.ControlFlow.Break
   residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     (verifier.Prepared × verifier.Accumulator)
     (core.convert.FromSame verifier.Error)
     residual

def queryEndR (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K)
 (i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 : U32) (r28 : verifier.Reader) : Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
 let (a21, r29) ←
   NJC_ConcreteUnwrap.raw 4#usize r28
 let i24 ← lift (core.num.U32.from_le_bytes a21)
 let (a22, r30) ←
   NJC_ConcreteUnwrap.raw 4#usize r29
 let i25 ← lift (core.num.U32.from_le_bytes a22)
 let (a23, r31) ←
   NJC_ConcreteUnwrap.raw 4#usize r30
 let i26 ← lift (core.num.U32.from_le_bytes a23)
 let (a24, r32) ←
   NJC_ConcreteUnwrap.raw 4#usize r31
 let i27 ← lift (core.num.U32.from_le_bytes a24)
 let (a25, r33) ←
   NJC_ConcreteUnwrap.raw 4#usize r32
 let i28 ← lift (core.num.U32.from_le_bytes a25)
 let (a26, r34) ←
   NJC_ConcreteUnwrap.raw 4#usize r33
 let i29 ← lift (core.num.U32.from_le_bytes a26)
 let queryValues := (Array.make 22#usize [
       i8, i9, i10, i11, i12, i13, i14, i15, i16,
       i17, i18, i19, i20, i21, i22, i23, i24,
       i25, i26, i27, i28, i29
       ])
 let r35 ←
   NJC_ValidateEmission.verifier.validate_checkpoint_queries
     queryValues
 let cf5 ←
   core.result.Result.Insts.CoreOpsTry.branch r35
 match cf5 with
 | core.ops.control_flow.ControlFlow.Continue _ =>
   finishTailR reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 queryValues r34
 | core.ops.control_flow.ControlFlow.Break
   residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     (verifier.Prepared × verifier.Accumulator)
     (core.convert.FromSame verifier.Error)
     residual

def queryMidG (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K)
 (i8 i9 i10 i11 i12 i13 i14 i15 : U32) (r20 : verifier.Reader) : NJU_Log.Run Event (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
 let (a13, r21) ←
   recordRaw 4#usize r20
 let i16 ← lift (core.num.U32.from_le_bytes a13)
 let (a14, r22) ←
   recordRaw 4#usize r21
 let i17 ← lift (core.num.U32.from_le_bytes a14)
 let (a15, r23) ←
   recordRaw 4#usize r22
 let i18 ← lift (core.num.U32.from_le_bytes a15)
 let (a16, r24) ←
   recordRaw 4#usize r23
 let i19 ← lift (core.num.U32.from_le_bytes a16)
 let (a17, r25) ←
   recordRaw 4#usize r24
 let i20 ← lift (core.num.U32.from_le_bytes a17)
 let (a18, r26) ←
   recordRaw 4#usize r25
 let i21 ← lift (core.num.U32.from_le_bytes a18)
 let (a19, r27) ←
   recordRaw 4#usize r26
 let i22 ← lift (core.num.U32.from_le_bytes a19)
 let (a20, r28) ←
   recordRaw 4#usize r27
 let i23 ← lift (core.num.U32.from_le_bytes a20)
 queryEndG reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 r28

def queryMidR (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K)
 (i8 i9 i10 i11 i12 i13 i14 i15 : U32) (r20 : verifier.Reader) : Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
 let (a13, r21) ←
   NJC_ConcreteUnwrap.raw 4#usize r20
 let i16 ← lift (core.num.U32.from_le_bytes a13)
 let (a14, r22) ←
   NJC_ConcreteUnwrap.raw 4#usize r21
 let i17 ← lift (core.num.U32.from_le_bytes a14)
 let (a15, r23) ←
   NJC_ConcreteUnwrap.raw 4#usize r22
 let i18 ← lift (core.num.U32.from_le_bytes a15)
 let (a16, r24) ←
   NJC_ConcreteUnwrap.raw 4#usize r23
 let i19 ← lift (core.num.U32.from_le_bytes a16)
 let (a17, r25) ←
   NJC_ConcreteUnwrap.raw 4#usize r24
 let i20 ← lift (core.num.U32.from_le_bytes a17)
 let (a18, r26) ←
   NJC_ConcreteUnwrap.raw 4#usize r25
 let i21 ← lift (core.num.U32.from_le_bytes a18)
 let (a19, r27) ←
   NJC_ConcreteUnwrap.raw 4#usize r26
 let i22 ← lift (core.num.U32.from_le_bytes a19)
 let (a20, r28) ←
   NJC_ConcreteUnwrap.raw 4#usize r27
 let i23 ← lift (core.num.U32.from_le_bytes a20)
 queryEndR reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 r28

def queryBlockG (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K)
 (r12 : verifier.Reader) : NJU_Log.Run Event (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
 let (a5, r13) ← recordRaw 4#usize r12
 let i8 ← lift (core.num.U32.from_le_bytes a5)
 let (a6, r14) ← recordRaw 4#usize r13
 let i9 ← lift (core.num.U32.from_le_bytes a6)
 let (a7, r15) ← recordRaw 4#usize r14
 let i10 ← lift (core.num.U32.from_le_bytes a7)
 let (a8, r16) ← recordRaw 4#usize r15
 let i11 ← lift (core.num.U32.from_le_bytes a8)
 let (a9, r17) ← recordRaw 4#usize r16
 let i12 ← lift (core.num.U32.from_le_bytes a9)
 let (a10, r18) ←
   recordRaw 4#usize r17
 let i13 ← lift (core.num.U32.from_le_bytes a10)
 let (a11, r19) ←
   recordRaw 4#usize r18
 let i14 ← lift (core.num.U32.from_le_bytes a11)
 let (a12, r20) ←
   recordRaw 4#usize r19
 let i15 ← lift (core.num.U32.from_le_bytes a12)
 queryMidG reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 i8 i9 i10 i11 i12 i13 i14 i15 r20

def queryBlockR (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K)
 (r12 : verifier.Reader) : Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
 let (a5, r13) ← NJC_ConcreteUnwrap.raw 4#usize r12
 let i8 ← lift (core.num.U32.from_le_bytes a5)
 let (a6, r14) ← NJC_ConcreteUnwrap.raw 4#usize r13
 let i9 ← lift (core.num.U32.from_le_bytes a6)
 let (a7, r15) ← NJC_ConcreteUnwrap.raw 4#usize r14
 let i10 ← lift (core.num.U32.from_le_bytes a7)
 let (a8, r16) ← NJC_ConcreteUnwrap.raw 4#usize r15
 let i11 ← lift (core.num.U32.from_le_bytes a8)
 let (a9, r17) ← NJC_ConcreteUnwrap.raw 4#usize r16
 let i12 ← lift (core.num.U32.from_le_bytes a9)
 let (a10, r18) ←
   NJC_ConcreteUnwrap.raw 4#usize r17
 let i13 ← lift (core.num.U32.from_le_bytes a10)
 let (a11, r19) ←
   NJC_ConcreteUnwrap.raw 4#usize r18
 let i14 ← lift (core.num.U32.from_le_bytes a11)
 let (a12, r20) ←
   NJC_ConcreteUnwrap.raw 4#usize r19
 let i15 ← lift (core.num.U32.from_le_bytes a12)
 queryMidR reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 i8 i9 i10 i11 i12 i13 i14 i15 r20

def resumeBodyG (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize) : NJU_Log.Run Event (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
 let (state, r) ←
   recordRaw 32#usize
     { bytes, «at» := 80#usize }
 let (a3, r1) ← recordRaw 32#usize r
 let (a4, r2) ← recordRaw 32#usize r1
 let (r3, r4) ← recordE r2
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r3
 match cf with
 | core.ops.control_flow.ControlFlow.Continue val =>
   let (r5, r6) ← recordE r4
   let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r5
   match cf1 with
   | core.ops.control_flow.ControlFlow.Continue val1 =>
     let (r7, r8) ← recordE r6
     let cf2 ←
       core.result.Result.Insts.CoreOpsTry.branch r7
     match cf2 with
     | core.ops.control_flow.ControlFlow.Continue val2 =>
       let (r9, r10) ← recordE r8
       let cf3 ←
         core.result.Result.Insts.CoreOpsTry.branch r9
       match cf3 with
       | core.ops.control_flow.ControlFlow.Continue val3 =>
         let (r11, r12) ← recordK r10
         let cf4 ←
           core.result.Result.Insts.CoreOpsTry.branch r11
         match cf4 with
         | core.ops.control_flow.ControlFlow.Continue val4
           =>
           queryBlockG reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 r12
         | core.ops.control_flow.ControlFlow.Break residual
           =>
           core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
             (verifier.Prepared × verifier.Accumulator)
             (core.convert.FromSame verifier.Error) residual
       | core.ops.control_flow.ControlFlow.Break residual =>
         core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
           (verifier.Prepared × verifier.Accumulator)
           (core.convert.FromSame verifier.Error) residual
     | core.ops.control_flow.ControlFlow.Break residual =>
       core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
         (verifier.Prepared × verifier.Accumulator)
         (core.convert.FromSame verifier.Error) residual
   | core.ops.control_flow.ControlFlow.Break residual =>
     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
       (verifier.Prepared × verifier.Accumulator)
       (core.convert.FromSame verifier.Error) residual
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     (verifier.Prepared × verifier.Accumulator)
     (core.convert.FromSame verifier.Error) residual

def resumeBodyR (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize) : Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
 let (state, r) ←
   NJC_ConcreteUnwrap.raw 32#usize
     { bytes, «at» := 80#usize }
 let (a3, r1) ← NJC_ConcreteUnwrap.raw 32#usize r
 let (a4, r2) ← NJC_ConcreteUnwrap.raw 32#usize r1
 let (r3, r4) ← NIL_FreshOps.readE r2
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r3
 match cf with
 | core.ops.control_flow.ControlFlow.Continue val =>
   let (r5, r6) ← NIL_FreshOps.readE r4
   let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r5
   match cf1 with
   | core.ops.control_flow.ControlFlow.Continue val1 =>
     let (r7, r8) ← NIL_FreshOps.readE r6
     let cf2 ←
       core.result.Result.Insts.CoreOpsTry.branch r7
     match cf2 with
     | core.ops.control_flow.ControlFlow.Continue val2 =>
       let (r9, r10) ← NIL_FreshOps.readE r8
       let cf3 ←
         core.result.Result.Insts.CoreOpsTry.branch r9
       match cf3 with
       | core.ops.control_flow.ControlFlow.Continue val3 =>
         let (r11, r12) ← NIL_FreshOps.readK r10
         let cf4 ←
           core.result.Result.Insts.CoreOpsTry.branch r11
         match cf4 with
         | core.ops.control_flow.ControlFlow.Continue val4
           =>
           queryBlockR reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 r12
         | core.ops.control_flow.ControlFlow.Break residual
           =>
           core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
             (verifier.Prepared × verifier.Accumulator)
             (core.convert.FromSame verifier.Error) residual
       | core.ops.control_flow.ControlFlow.Break residual =>
         core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
           (verifier.Prepared × verifier.Accumulator)
           (core.convert.FromSame verifier.Error) residual
     | core.ops.control_flow.ControlFlow.Break residual =>
       core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
         (verifier.Prepared × verifier.Accumulator)
         (core.convert.FromSame verifier.Error) residual
   | core.ops.control_flow.ControlFlow.Break residual =>
     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
       (verifier.Prepared × verifier.Accumulator)
       (core.convert.FromSame verifier.Error) residual
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     (verifier.Prepared × verifier.Accumulator)
     (core.convert.FromSame verifier.Error) residual

def run (reservation : NP6_StdModel.Reservation)
  {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
  (bytes : Slice Std.U8) (proof : Slice Std.U8) (public1 : Slice Std.U8)
  (v : transport.Variant) (hash : H) :
  NJU_Log.Run Event (core.result.Result (verifier.Prepared × verifier.Accumulator)
    verifier.Error)
  := do
  let i := Slice.len bytes
  let i1 ← (fun v=>CheckpointBytes4Ops.checkpointSize (NIL_Carriers.variant v)) v
  if i != i1
  then ok (core.result.Result.Err verifier.Error.Checkpoint)
  else
    let s ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes
        { «end» := 8#usize }
    let b ←
      core.cmp.impls.PartialEqShared.ne ((Slice.Insts.CoreCmpPartialEqArray CheckpointBytes4Ops.ne CheckpointBytes4Ops.eq)
        8#usize core.cmp.PartialEqU8) s
        (Array.make 8#usize [
          82#u8, 49#u8, 80#u8, 50#u8, 67#u8, 75#u8, 80#u8, 50#u8
          ])
    if b
    then ok (core.result.Result.Err verifier.Error.Checkpoint)
    else
      let i2 ← Slice.index_usize bytes 8#usize
      let i3 ← (fun v=>CheckpointBytes4Ops.tag (NIL_Carriers.variant v)) v
      if i2 != i3
      then ok (core.result.Result.Err verifier.Error.Checkpoint)
      else
        let i4 ← Slice.index_usize bytes 9#usize
        if i4 > 22#u8
        then ok (core.result.Result.Err verifier.Error.Checkpoint)
        else
          let i5 ← Slice.index_usize bytes 10#usize
          if i5 != 1#u8
          then ok (core.result.Result.Err verifier.Error.Checkpoint)
          else
            let s1 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                { start := 11#usize, «end» := 16#usize }
            let i6 ← core.slice.Slice.iter s1
            let (b1, _) ←
              recordAny
                (verifier.resume.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool
                (NIL_FreshOps.digest d)) i6 ()
            if b1
            then ok (core.result.Result.Err verifier.Error.Checkpoint)
            else
              let i7 := Slice.len bytes
              let end1 ← lift (Std.Usize.wrapping_sub i7 32#usize)
              let s2 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                  { start := 16#usize, «end» := 48#usize }
              let s3 ← lift (Array.to_slice (Array.make 1#usize [ proof ]))
              let a ← recordDigest d hash s3
              let b2 ←
                CheckpointBytes4Ops.ne core.cmp.PartialEqU8 s2 a
              if b2
              then ok (core.result.Result.Err verifier.Error.Checkpoint)
              else
                let s4 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                    { start := 48#usize, «end» := 80#usize }
                let s5 ←
                  lift (Array.to_slice (Array.make 1#usize [ public1 ]))
                let a1 ← recordDigest d hash s5
                let b3 ←
                  CheckpointBytes4Ops.ne core.cmp.PartialEqU8 s4
                    a1
                if b3
                then ok (core.result.Result.Err verifier.Error.Checkpoint)
                else
                  let s6 ←
                    core.slice.index.Slice.index
                      (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)
                      bytes { start := end1 }
                  let s7 ←
                    lift (Array.to_slice
                      (Array.make 22#usize [
                        85#u8, 78#u8, 80#u8, 82#u8, 79#u8, 86#u8, 69#u8, 68#u8,
                        58#u8, 82#u8, 49#u8, 58#u8, 99#u8, 104#u8, 101#u8,
                        99#u8, 107#u8, 112#u8, 111#u8, 105#u8, 110#u8, 116#u8
                        ]))
                  let s8 ←
                    core.slice.index.Slice.index
                      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)
                      bytes { «end» := end1 }
                  let s9 ←
                    lift (Array.to_slice (Array.make 2#usize [ s7, s8 ]))
                  let a2 ← recordDigest d hash s9
                  let b4 ←
                    CheckpointBytes4Ops.ne core.cmp.PartialEqU8
                      s6 a2
                  if b4
                  then ok (core.result.Result.Err verifier.Error.Checkpoint)
                  else
                    resumeBodyG reservation d bytes v i4 end1

def runRef (reservation : NP6_StdModel.Reservation)
  {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
  (bytes : Slice Std.U8) (proof : Slice Std.U8) (public1 : Slice Std.U8)
  (v : transport.Variant) (hash : H) :
  Result (core.result.Result (verifier.Prepared × verifier.Accumulator)
    verifier.Error)
  := do
  let i := Slice.len bytes
  let i1 ← (fun v=>CheckpointBytes4Ops.checkpointSize (NIL_Carriers.variant v)) v
  if i != i1
  then ok (core.result.Result.Err verifier.Error.Checkpoint)
  else
    let s ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes
        { «end» := 8#usize }
    let b ←
      core.cmp.impls.PartialEqShared.ne ((Slice.Insts.CoreCmpPartialEqArray CheckpointBytes4Ops.ne CheckpointBytes4Ops.eq)
        8#usize core.cmp.PartialEqU8) s
        (Array.make 8#usize [
          82#u8, 49#u8, 80#u8, 50#u8, 67#u8, 75#u8, 80#u8, 50#u8
          ])
    if b
    then ok (core.result.Result.Err verifier.Error.Checkpoint)
    else
      let i2 ← Slice.index_usize bytes 8#usize
      let i3 ← (fun v=>CheckpointBytes4Ops.tag (NIL_Carriers.variant v)) v
      if i2 != i3
      then ok (core.result.Result.Err verifier.Error.Checkpoint)
      else
        let i4 ← Slice.index_usize bytes 9#usize
        if i4 > 22#u8
        then ok (core.result.Result.Err verifier.Error.Checkpoint)
        else
          let i5 ← Slice.index_usize bytes 10#usize
          if i5 != 1#u8
          then ok (core.result.Result.Err verifier.Error.Checkpoint)
          else
            let s1 ←
              core.slice.index.Slice.index
                (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                { start := 11#usize, «end» := 16#usize }
            let i6 ← core.slice.Slice.iter s1
            let (b1, _) ←
              NIL_FreshOps.any
                (verifier.resume.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool
                (NIL_FreshOps.digest d)) i6 ()
            if b1
            then ok (core.result.Result.Err verifier.Error.Checkpoint)
            else
              let i7 := Slice.len bytes
              let end1 ← lift (Std.Usize.wrapping_sub i7 32#usize)
              let s2 ←
                core.slice.index.Slice.index
                  (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                  { start := 16#usize, «end» := 48#usize }
              let s3 ← lift (Array.to_slice (Array.make 1#usize [ proof ]))
              let a ← (NIL_FreshOps.digest d).digest hash s3
              let b2 ←
                CheckpointBytes4Ops.ne core.cmp.PartialEqU8 s2 a
              if b2
              then ok (core.result.Result.Err verifier.Error.Checkpoint)
              else
                let s4 ←
                  core.slice.index.Slice.index
                    (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes
                    { start := 48#usize, «end» := 80#usize }
                let s5 ←
                  lift (Array.to_slice (Array.make 1#usize [ public1 ]))
                let a1 ← (NIL_FreshOps.digest d).digest hash s5
                let b3 ←
                  CheckpointBytes4Ops.ne core.cmp.PartialEqU8 s4
                    a1
                if b3
                then ok (core.result.Result.Err verifier.Error.Checkpoint)
                else
                  let s6 ←
                    core.slice.index.Slice.index
                      (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8)
                      bytes { start := end1 }
                  let s7 ←
                    lift (Array.to_slice
                      (Array.make 22#usize [
                        85#u8, 78#u8, 80#u8, 82#u8, 79#u8, 86#u8, 69#u8, 68#u8,
                        58#u8, 82#u8, 49#u8, 58#u8, 99#u8, 104#u8, 101#u8,
                        99#u8, 107#u8, 112#u8, 111#u8, 105#u8, 110#u8, 116#u8
                        ]))
                  let s8 ←
                    core.slice.index.Slice.index
                      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)
                      bytes { «end» := end1 }
                  let s9 ←
                    lift (Array.to_slice (Array.make 2#usize [ s7, s8 ]))
                  let a2 ← (NIL_FreshOps.digest d).digest hash s9
                  let b4 ←
                    CheckpointBytes4Ops.ne core.cmp.PartialEqU8
                      s6 a2
                  if b4
                  then ok (core.result.Result.Err verifier.Error.Checkpoint)
                  else
                    resumeBodyR reservation d bytes v i4 end1

/-- The outlined plain reference is definitionally the retained source. No
new extraction or changed source model is used. -/
theorem reference (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (ck proof pub : Slice U8) (v : transport.Variant) (hash : H) :
 runRef reservation d ck proof pub v hash=
 NJC_RawCalls.resume (NJC_FilledClause.reserved reservation) d ck proof pub v hash := by
 rfl

#print axioms reference
end NJU_ResumeObserved
