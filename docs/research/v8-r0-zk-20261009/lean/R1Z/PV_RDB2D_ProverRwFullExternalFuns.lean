import R1Z.PV_RDB2D_ProverRwFullTypes
open Aeneas Aeneas.Std Result ControlFlow Error
namespace ProverRwFull

class ExternalFuns [ExternalTypes] where
  op0 {T : Type} {U : Type} (AsRefInst : core.convert.AsRef T U) : T → Result U
  op1 {T : Type} : (Slice T) → Result (Slice T)
  op2 : core.io.error.ErrorKind → core.io.error.ErrorKind → Result Bool
  op3 {T : Type} (defaultDefaultInst : core.default.Default T) :
      T → Result (T × T)
  op4 {T : Type} : T → Result Unit
  op5 {T : Type} {T1 : Type} (opsfunctionFnOnceT1TupleTBoolInst :
      core.ops.function.FnOnce T1 T Bool) :
      (Option T) → T1 → Result Bool
  op6 {T : Type} : (Option T) → Result (Option T)
  op7 {T : Type} {E : Type} : (Option T) → E → Result (core.result.Result T E)
  op8 {T : Type} (cmpPartialEqInst : core.cmp.PartialEq T T) :
      (Option T) → (Option T) → Result Bool
  op9 {T : Type} :
      (Option T) → Result (core.ops.control_flow.ControlFlow (Option
        core.convert.Infallible) T)
  op10 (T : Type) : (Option core.convert.Infallible) → Result (Option T)
  op11 {T : Type} {E : Type} {U : Type} {F : Type} (opsfunctionFnOnceFTupleTUInst :
      core.ops.function.FnOnce F T U) :
      (core.result.Result T E) → F → Result (core.result.Result U E)
  op12 {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
      core.ops.function.FnOnce O E F) :
      (core.result.Result T E) → O → Result (core.result.Result T F)
  op13 : core.sync.atomic.Ordering → Result Unit
  op14 {P : Type} (coreconvertAsRefPPathInst : core.convert.AsRef P std.path.Path) :
      P → Result (core.result.Result std.fs.File std.io.error.Error)
  op15 : std.fs.File → Result (core.result.Result Unit std.io.error.Error)
  op16 {Self : Type} (WriteInst : std.io.Write Self) :
      Self → (Slice Std.U8) → Result ((core.result.Result Unit
        std.io.error.Error) × Self)
  op17 :
      std.fs.File → Result ((core.result.Result Unit std.io.error.Error) ×
        std.fs.File)
  op18 :
      std.fs.File → (Slice Std.U8) → Result ((core.result.Result Std.Usize
        std.io.error.Error) × std.fs.File)
  op19 : Result std.fs.OpenOptions
  op20 :
      std.fs.OpenOptions → Bool → Result (std.fs.OpenOptions ×
        (std.fs.OpenOptions → std.fs.OpenOptions))
  op21 :
      std.fs.OpenOptions → Bool → Result (std.fs.OpenOptions ×
        (std.fs.OpenOptions → std.fs.OpenOptions))
  op22 {P : Type} (coreconvertAsRefPPathInst : core.convert.AsRef P std.path.Path) :
      std.fs.OpenOptions → P → Result (core.result.Result std.fs.File
        std.io.error.Error)
  op23 : std.io.error.Error → Result core.io.error.ErrorKind
  op24 :
      std.fs.OpenOptions → Std.U32 → Result (std.fs.OpenOptions ×
        (std.fs.OpenOptions → std.fs.OpenOptions))
  op25 : std.path.PathBuf → Result std.path.Path
  op26 {P : Type} (coreconvertAsRefPPathInst : core.convert.AsRef P std.path.Path) :
      std.path.Path → P → Result std.path.PathBuf
  op27 : std.path.Path → Result std.path.Path
  op28 : String → Result std.path.Path
  op29 : std.path.PathBuf → Result std.path.Path
  op30 : Std.Usize → Result String
  op31 : String → Str → Result String
  op32 {T : Type} (A : Type) :
      (alloc.vec.Vec T) → Std.Usize → Result ((core.result.Result Unit
        alloc.collections.TryReserveError) × (alloc.vec.Vec T))
  op33 {T : Type} (A : Type) :
      (alloc.vec.Vec T) → Result ((Option T) × (alloc.vec.Vec T))
  op34 {T : Type} (A : Type) : (alloc.vec.Vec T) → Result Bool
  op35 (T : Type) : Result (alloc.vec.Vec T)
  op36 {T : Type} (A : Type) (N : Std.Usize) :
      (alloc.vec.Vec T) → Result (core.result.Result (Array T N) (alloc.vec.Vec
        T))
  op37 :
      aspis_core.circle.SecureCirclePoint → aspis_core.circle.SecureCirclePoint
        → Result Bool
  op38 : aspis_core.digest.LegacyHashFn → Result aspis_core.digest.LegacyHashFn
  op39 :
      aspis_core.digest.LegacyHashFn → (Slice (Slice Std.U8)) → Result (Array
        Std.U8 32#usize)
  op40 :
      aspis_core.field.wide_exact.WideExact → Result
        aspis_core.field.wide_exact.WideExact
  op41 :
      aspis_core.field.wide_exact.WideExact →
        aspis_core.field.wide_exact.WideExact → Result Bool
  op42 : Result aspis_core.field.wide_exact.WideExact
  op43 : aspis_core.field.wide_exact.WideExact → Result aspis_core.field.QM31
  op44 : aspis_core.field.wide_exact.WideExact → Result aspis_core.field.QM31
  op45 : aspis_core.field.QM31 → Result aspis_core.field.wide_exact.WideExact
  op46 :
      aspis_core.field.wide_exact.WideExact →
        aspis_core.field.wide_exact.WideExact → Result
        aspis_core.field.wide_exact.WideExact
  op47 :
      aspis_core.field.wide_exact.WideExact →
        aspis_core.field.wide_exact.WideExact → Result
        aspis_core.field.wide_exact.WideExact
  op48 :
      aspis_core.field.wide_exact.WideExact → aspis_core.field.QM31 → Result
        aspis_core.field.wide_exact.WideExact
  op49 : aspis_core.field.wide_exact.WideExact → Result (Array Std.U32 8#usize)
  op50 : (Slice Std.U8) → Result (Option aspis_core.field.wide_exact.WideExact)
  op51 : aspis_core.field.wide_exact.WideExact → Result (Array Std.U8 32#usize)
  op52 :
      aspis_core.field.wide_exact.WideExact → aspis_core.field.M31 → Result
        aspis_core.field.wide_exact.WideExact
  op53 : aspis_core.field.M31 → Result aspis_core.field.M31
  op54 : aspis_core.field.M31 → aspis_core.field.M31 → Result Bool
  op55 : Result aspis_core.field.M31
  op56 : Result aspis_core.field.M31
  op57 :
      aspis_core.field.M31 → aspis_core.field.M31 → Result aspis_core.field.M31
  op58 : aspis_core.field.M31 → Result aspis_core.field.M31
  op59 : aspis_core.field.M31 → Result aspis_core.field.M31
  op60 :
      aspis_core.field.M31 → aspis_core.field.M31 → Result
        aspis_core.field.CM31
  op61 : aspis_core.field.M31 → Result aspis_core.field.CM31
  op62 : aspis_core.field.QM31 → Result aspis_core.field.QM31
  op63 : aspis_core.field.QM31 → aspis_core.field.QM31 → Result Bool
  op64 : Result aspis_core.field.QM31
  op65 : Result aspis_core.field.QM31
  op66 : aspis_core.field.CM31 → Result aspis_core.field.QM31
  op67 :
      aspis_core.field.QM31 → aspis_core.field.QM31 → Result
        aspis_core.field.QM31
  op68 :
      aspis_core.field.QM31 → aspis_core.field.QM31 → Result
        aspis_core.field.QM31
  op69 :
      aspis_core.field.QM31 → aspis_core.field.QM31 → Result
        aspis_core.field.QM31
  op70 :
      aspis_core.field.QM31 → aspis_core.field.M31 → Result
        aspis_core.field.QM31
  op71 : (Slice Std.U8) → Result (Option aspis_core.field.QM31)
  op72 : aspis_core.field.QM31 → (Slice Std.U8) → Result (Slice Std.U8)
  op73 :
      aspis_core.field.M31 → aspis_core.field.M31 → Result aspis_core.field.M31
  op74 :
      aspis_core.field.M31 → aspis_core.field.M31 → Result aspis_core.field.M31
  op75 :
      Std.Usize → Result (core.result.Result aspis_core.r0.domain.FibreIndex
        aspis_core.r0.Error)
  op76 : aspis_core.r0.domain.FibreIndex → Result Std.Usize
  op77 {E : Type} (corecloneCloneInst : core.clone.Clone E) :
      (aspis_core.r0.domain.Point E) → Result (aspis_core.r0.domain.Point E)
  op78 {E : Type} (scalarCodeFieldInst : aspis_core.r0.scalar.CodeField E) :
      aspis_core.r0.domain.FibreIndex → Result (aspis_core.r0.domain.Point E)
  op79 {E : Type} (scalarCodeFieldInst : aspis_core.r0.scalar.CodeField E) :
      (Array E 1024#usize) → (aspis_core.r0.domain.Point E) → Result E
  op80 {E : Type} (scalarCodeFieldInst : aspis_core.r0.scalar.CodeField E) :
      E → E → (Array E 4#usize) → Result (Array E 4#usize)
  op81 {T : Type} (coremarkerCopyInst : core.marker.Copy T) :
      Std.Usize → T → Result (core.result.Result (alloc.vec.Vec T)
        aspis_core.r0.Error)
  op82 : Result Std.U8
  op83 : Result Std.U8
  op84 :
      (Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) → Std.U8 →
        (Slice Std.U8) → Result (Array Std.U8 32#usize)
  op85 :
      aspis_core.r0.Error → core.fmt.Formatter → Result ((core.result.Result
        Unit core.fmt.Error) × core.fmt.Formatter)
  op86 : Result Std.Usize
  op87 : Result aspis_core.field.M31
  op88 : Result aspis_core.field.wide_exact.WideExact
  op89 : Result aspis_core.field.QM31
  op90 : Result aspis_core.field.M31
  op91 : Result aspis_core.field.wide_exact.WideExact
  op92 : Result aspis_core.field.QM31
  op93 :
      aspis_core.field.M31 → aspis_core.field.M31 → Result aspis_core.field.M31
  op94 :
      aspis_core.field.wide_exact.WideExact →
        aspis_core.field.wide_exact.WideExact → Result
        aspis_core.field.wide_exact.WideExact
  op95 :
      aspis_core.field.QM31 → aspis_core.field.QM31 → Result
        aspis_core.field.QM31
  op96 :
      aspis_core.field.M31 → aspis_core.field.M31 → Result aspis_core.field.M31
  op97 :
      aspis_core.field.wide_exact.WideExact →
        aspis_core.field.wide_exact.WideExact → Result
        aspis_core.field.wide_exact.WideExact
  op98 :
      aspis_core.field.QM31 → aspis_core.field.QM31 → Result
        aspis_core.field.QM31
  op99 : aspis_core.field.M31 → Result aspis_core.field.M31
  op100 :
      aspis_core.field.wide_exact.WideExact → Result
        aspis_core.field.wide_exact.WideExact
  op101 : aspis_core.field.QM31 → Result aspis_core.field.QM31
  op102 :
      aspis_core.field.M31 → aspis_core.field.M31 → Result aspis_core.field.M31
  op103 :
      aspis_core.field.wide_exact.WideExact →
        aspis_core.field.wide_exact.WideExact → Result
        aspis_core.field.wide_exact.WideExact
  op104 :
      aspis_core.field.QM31 → aspis_core.field.QM31 → Result
        aspis_core.field.QM31
  op105 : aspis_core.field.M31 → Result (Option aspis_core.field.M31)
  op106 : aspis_core.field.M31 → Result aspis_core.field.M31
  op107 : aspis_core.field.QM31 → Result (Option aspis_core.field.QM31)
  op108 : aspis_core.field.M31 → Result aspis_core.field.QM31
  op109 :
      aspis_core.field.wide_exact.WideExact → Result (Option
        aspis_core.field.wide_exact.WideExact)
  op110 : aspis_core.field.M31 → Result aspis_core.field.wide_exact.WideExact
  op111 : Result Std.U64
  op112 : Result Std.U64
  op113 : Result Std.U64
  op114 :
      aspis_core.state_only_hiding.StateOnlyHidingContext →
        aspis_core.state_only_hiding.StateOnlyHidingContext → Result Bool
  op115 :
      (Array Std.U8 32#usize) → (Array Std.U8 32#usize) → Result
        aspis_core.state_only_hiding.StateOnlyHidingContext
  op116 :
      aspis_core.state_only_hiding.StateOnlyHidingContext → Result (Array Std.U8
        81#usize)
  op117 :
      (Array aspis_core.field.QM31 16#usize) → (Array aspis_core.field.QM31
        10#usize) → aspis_core.field.QM31 → (Array aspis_core.field.QM31
        10#usize) → Result aspis_core.field.QM31
  op118 :
      (Array aspis_core.field.QM31 10#usize) → Result (Array (Array
        aspis_core.field.QM31 10#usize) 3#usize)
  op119 :
      (Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) → Std.U8 →
        (Slice Std.U8) → (Array Std.U8 32#usize) → Result (Array Std.U8
        32#usize)
  op120 : (Array aspis_core.field.QM31 28#usize) → Result aspis_core.field.QM31
  op121 :
      (Array aspis_core.field.QM31 28#usize) → aspis_core.field.QM31 → Result
        aspis_core.field.QM31
  op122 {Z : Type} {N : Std.Usize} (ZeroizeInst : zeroize.Zeroize Z) :
      (Array Z N) → Result (Array Z N)
  op123 {Z : Type} (DefaultIsZeroesInst : zeroize.DefaultIsZeroes Z) : Z → Result Z
  op124 {T : Type} (coremarkerCopyInst : core.marker.Copy T) : T → T → Result T
  op125 {T : Type} {Z : Type} (coreconvertAsMutInst : core.convert.AsMut Z T)
      (ZeroizeInst : zeroize.Zeroize Z) :
      (zeroize.Zeroizing Z) → Result (T × (T → zeroize.Zeroizing Z))
  op126 {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) :
      (zeroize.Zeroizing Z) → Result (Z × (Z → zeroize.Zeroizing Z))
  op127 {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) :
      (zeroize.Zeroizing Z) → Result Z
  op128 {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) :
      Z → Result (zeroize.Zeroizing Z)
  op129 :
      (Slice Std.U8) → Result ((core.result.Result Unit getrandom.error.Error) ×
        (Slice Std.U8))
  op130 {Z : Type} (ZeroizeInst : zeroize.Zeroize Z) :
      (zeroize.Zeroizing Z) → Result (zeroize.Zeroizing Z)
  op131 {T : Type} {Z : Type} (coreconvertAsRefInst : core.convert.AsRef Z T)
      (ZeroizeInst : zeroize.Zeroize Z) :
      (zeroize.Zeroizing Z) → Result T
  op132 :
      Result (core.result.Result (alloc.vec.Vec aspis_statement.trace_v4.TraceCell)
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1)
  op133 :
      Result (core.result.Result (alloc.vec.Vec Std.U16)
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1)
  op134 :
      Result (core.result.Result (Array Std.U16 64#usize)
        aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1)
  op135 {SoFar : Type} (marker_traitsOrdInst : typenum.marker_traits.Ord SoFar) :
      typenum.uint.UTerm → typenum.uint.UTerm → SoFar → Result SoFar
  op136 {U : Type} {B : Type} {SoFar : Type} (marker_traitsUnsignedInst :
      typenum.marker_traits.Unsigned U) (marker_traitsBitInst :
      typenum.marker_traits.Bit B) (marker_traitsOrdInst :
      typenum.marker_traits.Ord SoFar) :
      typenum.uint.UTerm → (typenum.uint.UInt U B) → SoFar → Result
        typenum.Less
  op137 {Ul : Type} {Ur : Type} {SoFar : Type} {Clause3_Output : Type}
      (marker_traitsUnsignedInst : typenum.marker_traits.Unsigned Ul)
      (marker_traitsUnsignedInst1 : typenum.marker_traits.Unsigned Ur)
      (marker_traitsOrdInst : typenum.marker_traits.Ord SoFar)
      (privatePrivateCmpUlUrGreaterClause3_OutputInst : typenum.private.PrivateCmp
      Ul Ur typenum.Greater Clause3_Output) :
      (typenum.uint.UInt Ul typenum.bit.B1) → (typenum.uint.UInt Ur
        typenum.bit.B0) → SoFar → Result Clause3_Output
  op138 {Ul : Type} {Ur : Type} {SoFar : Type} {Clause3_Output : Type}
      (marker_traitsUnsignedInst : typenum.marker_traits.Unsigned Ul)
      (marker_traitsUnsignedInst1 : typenum.marker_traits.Unsigned Ur)
      (marker_traitsOrdInst : typenum.marker_traits.Ord SoFar)
      (privatePrivateCmpInst : typenum.private.PrivateCmp Ul Ur SoFar
      Clause3_Output) :
      (typenum.uint.UInt Ul typenum.bit.B1) → (typenum.uint.UInt Ur
        typenum.bit.B1) → SoFar → Result Clause3_Output
  op139 {Ul : Type} {Ur : Type} {SoFar : Type} {Clause3_Output : Type}
      (marker_traitsUnsignedInst : typenum.marker_traits.Unsigned Ul)
      (marker_traitsUnsignedInst1 : typenum.marker_traits.Unsigned Ur)
      (marker_traitsOrdInst : typenum.marker_traits.Ord SoFar)
      (privatePrivateCmpInst : typenum.private.PrivateCmp Ul Ur SoFar
      Clause3_Output) :
      (typenum.uint.UInt Ul typenum.bit.B0) → (typenum.uint.UInt Ur
        typenum.bit.B0) → SoFar → Result Clause3_Output
  op140 {Ul : Type} {Ur : Type} {IM : Type} {Clause2_Output : Type}
      (marker_traitsUnsignedInst : typenum.marker_traits.Unsigned Ul)
      (marker_traitsUnsignedInst1 : typenum.marker_traits.Unsigned Ur)
      (privatePrivateCmpUlUrEqualClause2_OutputInst : typenum.private.PrivateCmp Ul
      Ur typenum.Equal Clause2_Output) (privateInternalMarkerInst :
      typenum.private.InternalMarker IM) :
      (typenum.uint.UInt Ul typenum.bit.B0) → (typenum.uint.UInt Ur
        typenum.bit.B0) → Result Clause2_Output
  op141 {U : Type} {B : Type} (marker_traitsUnsignedInst :
      typenum.marker_traits.Unsigned U) (marker_traitsBitInst :
      typenum.marker_traits.Bit B) :
      Result Std.Isize
  op142 {U : Type} {B : Type} (marker_traitsUnsignedInst :
      typenum.marker_traits.Unsigned U) (marker_traitsBitInst :
      typenum.marker_traits.Bit B) :
      Result Std.I64
  op143 {U : Type} {B : Type} (marker_traitsUnsignedInst :
      typenum.marker_traits.Unsigned U) (marker_traitsBitInst :
      typenum.marker_traits.Bit B) :
      Result Std.I32
  op144 {U : Type} {B : Type} (marker_traitsUnsignedInst :
      typenum.marker_traits.Unsigned U) (marker_traitsBitInst :
      typenum.marker_traits.Bit B) :
      Result Std.I16
  op145 {U : Type} {B : Type} (marker_traitsUnsignedInst :
      typenum.marker_traits.Unsigned U) (marker_traitsBitInst :
      typenum.marker_traits.Bit B) :
      Result Std.I8
  op146 {U : Type} {B : Type} (marker_traitsUnsignedInst :
      typenum.marker_traits.Unsigned U) (marker_traitsBitInst :
      typenum.marker_traits.Bit B) :
      Result Std.Usize
  op147 {U : Type} {B : Type} (marker_traitsUnsignedInst :
      typenum.marker_traits.Unsigned U) (marker_traitsBitInst :
      typenum.marker_traits.Bit B) :
      Result Std.U64
  op148 {U : Type} {B : Type} (marker_traitsUnsignedInst :
      typenum.marker_traits.Unsigned U) (marker_traitsBitInst :
      typenum.marker_traits.Bit B) :
      Result Std.U32
  op149 {U : Type} {B : Type} (marker_traitsUnsignedInst :
      typenum.marker_traits.Unsigned U) (marker_traitsBitInst :
      typenum.marker_traits.Bit B) :
      Result Std.U16
  op150 {U : Type} {B : Type} (marker_traitsUnsignedInst :
      typenum.marker_traits.Unsigned U) (marker_traitsBitInst :
      typenum.marker_traits.Bit B) :
      Result Std.U8
  op151 {U : Type} {B
      : Type} (marker_traitsUnsignedInst : typenum.marker_traits.Unsigned U)
      (marker_traitsBitInst : typenum.marker_traits.Bit B) : Result Std.Isize
  op152 {U : Type} {B :
      Type} (marker_traitsUnsignedInst : typenum.marker_traits.Unsigned U)
      (marker_traitsBitInst : typenum.marker_traits.Bit B) : Result Std.I64
  op153 {U : Type} {B :
      Type} (marker_traitsUnsignedInst : typenum.marker_traits.Unsigned U)
      (marker_traitsBitInst : typenum.marker_traits.Bit B) : Result Std.I32
  op154 {U : Type} {B :
      Type} (marker_traitsUnsignedInst : typenum.marker_traits.Unsigned U)
      (marker_traitsBitInst : typenum.marker_traits.Bit B) : Result Std.I16
  op155 {U : Type} {B :
      Type} (marker_traitsUnsignedInst : typenum.marker_traits.Unsigned U)
      (marker_traitsBitInst : typenum.marker_traits.Bit B) : Result Std.I8
  op156 {U : Type} {B
      : Type} (marker_traitsUnsignedInst : typenum.marker_traits.Unsigned U)
      (marker_traitsBitInst : typenum.marker_traits.Bit B) : Result Std.Usize
  op157 {U : Type} {B :
      Type} (marker_traitsUnsignedInst : typenum.marker_traits.Unsigned U)
      (marker_traitsBitInst : typenum.marker_traits.Bit B) : Result Std.U64
  op158 {U : Type} {B :
      Type} (marker_traitsUnsignedInst : typenum.marker_traits.Unsigned U)
      (marker_traitsBitInst : typenum.marker_traits.Bit B) : Result Std.U32
  op159 {U : Type} {B :
      Type} (marker_traitsUnsignedInst : typenum.marker_traits.Unsigned U)
      (marker_traitsBitInst : typenum.marker_traits.Bit B) : Result Std.U16
  op160 {U : Type} {B :
      Type} (marker_traitsUnsignedInst : typenum.marker_traits.Unsigned U)
      (marker_traitsBitInst : typenum.marker_traits.Bit B) : Result Std.U8
  op161 {U : Type} {B : Type} (coredefaultDefaultInst : core.default.Default U)
      (coredefaultDefaultInst1 : core.default.Default B) :
      Result (typenum.uint.UInt U B)
  op162 {U : Type} {B : Type} (corecloneCloneInst : core.clone.Clone U)
      (corecloneCloneInst1 : core.clone.Clone B) :
      (typenum.uint.UInt U B) → Result (typenum.uint.UInt U B)
  op163 : Result Std.Isize
  op164 : Result Std.I64
  op165 : Result Std.I32
  op166 : Result Std.I16
  op167 : Result Std.I8
  op168 : Result Std.Usize
  op169 : Result Std.U64
  op170 : Result Std.U32
  op171 : Result Std.U16
  op172 : Result Std.U8
  op173 : Result Std.Isize
  op174 : Result Std.I64
  op175 : Result Std.I32
  op176 : Result Std.I16
  op177 : Result Std.I8
  op178 : Result Std.Usize
  op179 : Result Std.U64
  op180 : Result Std.U32
  op181 : Result Std.U16
  op182 : Result Std.U8
  op183 : Result typenum.uint.UTerm
  op184 : typenum.uint.UTerm → Result typenum.uint.UTerm
  op185 {A : Type} {B : Type} {Clause0_Output : Type} {Clause1_Output : Type}
      (CmpInst : typenum.type_operators.Cmp A B Clause0_Output)
      (privateIsLessOrEqualPrivateInst : typenum.private.IsLessOrEqualPrivate A B
      Clause0_Output Clause1_Output) :
      A → B → Result Clause1_Output
  op186 {A : Type} {B : Type} {Clause0_Output : Type} {Clause1_Output : Type}
      (CmpInst : typenum.type_operators.Cmp A B Clause0_Output)
      (privateIsLessPrivateInst : typenum.private.IsLessPrivate A B Clause0_Output
      Clause1_Output) :
      A → B → Result Clause1_Output
  op187 {A : Type} {B : Type} : A → B → typenum.Equal → Result typenum.bit.B1
  op188 : Result Bool
  op189 : Result Std.U8
  op190 : Result typenum.bit.B1
  op191 : Result Bool
  op192 : Result Std.U8
  op193 : Result typenum.bit.B1
  op194 : typenum.bit.B1 → Result typenum.bit.B1
  op195 {A : Type} {B : Type} : A → B → typenum.Less → Result typenum.bit.B1
  op196 : Result Ordering
  op197 : Result Ordering
  op198 : Result Bool
  op199 : Result Std.U8
  op200 : Result typenum.bit.B0
  op201 : Result Bool
  op202 : Result Std.U8
  op203 : Result typenum.bit.B0
  op204 : typenum.bit.B0 → Result typenum.bit.B0
  op205 :
      sha2.core_api.Sha256VarCore → (block_buffer.BlockBuffer (typenum.uint.UInt
        (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt
        (typenum.uint.UInt (typenum.uint.UInt typenum.uint.UTerm typenum.bit.B1)
        typenum.bit.B0) typenum.bit.B0) typenum.bit.B0) typenum.bit.B0)
        typenum.bit.B0) typenum.bit.B0) block_buffer.Eager
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplOdd Std.U8 (Array Std.U8 0#usize))))))))
        typenum.bit.B1) → (generic_array.GenericArray Std.U8 (typenum.uint.UInt
        (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt
        (typenum.uint.UInt typenum.uint.UTerm typenum.bit.B1) typenum.bit.B0)
        typenum.bit.B0) typenum.bit.B0) typenum.bit.B0) typenum.bit.B0)
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplOdd Std.U8 (Array Std.U8 0#usize)))))))) →
        Result (sha2.core_api.Sha256VarCore × (block_buffer.BlockBuffer
        (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt
        (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt typenum.uint.UTerm
        typenum.bit.B1) typenum.bit.B0) typenum.bit.B0) typenum.bit.B0)
        typenum.bit.B0) typenum.bit.B0) typenum.bit.B0) block_buffer.Eager
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplOdd Std.U8 (Array Std.U8 0#usize))))))))
        typenum.bit.B1) × (generic_array.GenericArray Std.U8 (typenum.uint.UInt
        (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt
        (typenum.uint.UInt typenum.uint.UTerm typenum.bit.B1) typenum.bit.B0)
        typenum.bit.B0) typenum.bit.B0) typenum.bit.B0) typenum.bit.B0)
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplOdd Std.U8 (Array Std.U8 0#usize)))))))))
  op206 :
      Std.Usize → Result (core.result.Result sha2.core_api.Sha256VarCore
        digest.InvalidOutputSize)
  op207 : Result digest.core_api.TruncSide
  op208 :
      sha2.core_api.Sha256VarCore → (Slice (generic_array.GenericArray Std.U8
        (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt
        (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt typenum.uint.UTerm
        typenum.bit.B1) typenum.bit.B0) typenum.bit.B0) typenum.bit.B0)
        typenum.bit.B0) typenum.bit.B0) typenum.bit.B0)
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplEven Std.U8
        (generic_array.GenericArrayImplOdd Std.U8 (Array Std.U8 0#usize))))))))))
        → Result sha2.core_api.Sha256VarCore
  op209 {N : Type} {Clause0_ArrayType : Type}
      (generic_arrayArrayLengthNU8Clause0_ArrayTypeInst : generic_array.ArrayLength
      N Std.U8 Clause0_ArrayType) :
      (Slice Std.U8) → Result ((Slice (generic_array.GenericArray Std.U8 N
        Clause0_ArrayType)) × (Slice Std.U8))
  op210 : Std.Usize → Std.Usize → Result Bool
  op211 {T : Type} :
      (generic_array.GenericArray T (typenum.uint.UInt (typenum.uint.UInt
        (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt
        typenum.uint.UTerm typenum.bit.B1) typenum.bit.B0) typenum.bit.B0)
        typenum.bit.B0) typenum.bit.B0) typenum.bit.B0)
        (generic_array.GenericArrayImplEven T (generic_array.GenericArrayImplEven T
        (generic_array.GenericArrayImplEven T (generic_array.GenericArrayImplEven T
        (generic_array.GenericArrayImplEven T (generic_array.GenericArrayImplOdd T
        (Array T 0#usize)))))))) → Result (Array T 32#usize)
  op212 {D : Type} {Clause0_Clause1_OutputSize : Type}
      {Clause0_Clause1_Clause0_ArrayType : Type} (FixedOutputInst :
      digest.FixedOutput D Clause0_Clause1_OutputSize
      Clause0_Clause1_Clause0_ArrayType) (coredefaultDefaultInst :
      core.default.Default D) (UpdateInst : digest.Update D) (HashMarkerInst :
      digest.digest.HashMarker D) :
      D → Result (generic_array.GenericArray Std.U8 Clause0_Clause1_OutputSize
        Clause0_Clause1_Clause0_ArrayType)
  op213 {D : Type} {T1 : Type} {Clause0_Clause1_OutputSize : Type}
      {Clause0_Clause1_Clause0_ArrayType : Type} (FixedOutputInst :
      digest.FixedOutput D Clause0_Clause1_OutputSize
      Clause0_Clause1_Clause0_ArrayType) (coredefaultDefaultInst :
      core.default.Default D) (UpdateInst : digest.Update D) (HashMarkerInst :
      digest.digest.HashMarker D) (coreconvertAsRefT1SliceU8Inst :
      core.convert.AsRef T1 (Slice Std.U8)) :
      D → T1 → Result D
  op214 {D : Type} {Clause0_Clause1_OutputSize : Type}
      {Clause0_Clause1_Clause0_ArrayType : Type} (FixedOutputInst :
      digest.FixedOutput D Clause0_Clause1_OutputSize
      Clause0_Clause1_Clause0_ArrayType) (coredefaultDefaultInst :
      core.default.Default D) (UpdateInst : digest.Update D) (HashMarkerInst :
      digest.digest.HashMarker D) :
      Result D
  op215 {T : Type} {Clause0_Clause0_Clause0_BlockSize : Type}
      {Clause0_Clause0_Clause0_Clause0_ArrayType : Type}
      {Clause0_Clause1_BufferKind : Type} {Clause0_Clause1_Clause0_BlockSize :
      Type} {Clause0_Clause1_Clause0_Clause0_ArrayType : Type}
      {Clause0_Clause2_OutputSize : Type} {Clause0_Clause2_Clause0_ArrayType :
      Type} {Clause0_Clause3_Output : Type} {Clause1_Output : Type}
      (FixedOutputCoreInst : digest.core_api.FixedOutputCore T
      Clause0_Clause0_Clause0_BlockSize Clause0_Clause0_Clause0_Clause0_ArrayType
      Clause0_Clause1_BufferKind Clause0_Clause1_Clause0_BlockSize
      Clause0_Clause1_Clause0_Clause0_ArrayType Clause0_Clause2_OutputSize
      Clause0_Clause2_Clause0_ArrayType Clause0_Clause3_Output)
      (typenumtype_operatorsIsLessClause0_Clause0_Clause0_BlockSizeUIntUIntUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0B0B0Clause1_OutputInst
      : typenum.type_operators.IsLess Clause0_Clause0_Clause0_BlockSize
      (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt
      (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt
      (typenum.uint.UInt typenum.uint.UTerm typenum.bit.B1) typenum.bit.B0)
      typenum.bit.B0) typenum.bit.B0) typenum.bit.B0) typenum.bit.B0)
      typenum.bit.B0) typenum.bit.B0) typenum.bit.B0) Clause1_Output)
      (typenummarker_traitsNonZeroInst : typenum.marker_traits.NonZero
      Clause1_Output) :
      (digest.core_api.wrapper.CoreWrapper T Clause0_Clause1_BufferKind
        Clause0_Clause1_Clause0_BlockSize Clause0_Clause1_Clause0_Clause0_ArrayType
        Clause1_Output) → (generic_array.GenericArray Std.U8
        Clause0_Clause2_OutputSize Clause0_Clause2_Clause0_ArrayType) → Result
        (generic_array.GenericArray Std.U8 Clause0_Clause2_OutputSize
        Clause0_Clause2_Clause0_ArrayType)
  op216 {T : Type} {Clause0_BufferKind : Type} {Clause0_Clause0_BlockSize : Type}
      {Clause0_Clause0_Clause0_ArrayType : Type} {Clause1_Clause0_BlockSize : Type}
      {Clause1_Clause0_Clause0_ArrayType : Type} {Clause2_Output : Type}
      (BufferKindUserInst : digest.core_api.BufferKindUser T Clause0_BufferKind
      Clause0_Clause0_BlockSize Clause0_Clause0_Clause0_ArrayType) (UpdateCoreInst
      : digest.core_api.UpdateCore T Clause1_Clause0_BlockSize
      Clause1_Clause0_Clause0_ArrayType)
      (typenumtype_operatorsIsLessClause0_Clause0_BlockSizeUIntUIntUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0B0B0Clause2_OutputInst
      : typenum.type_operators.IsLess Clause0_Clause0_BlockSize (typenum.uint.UInt
      (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt
      (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt
      typenum.uint.UTerm typenum.bit.B1) typenum.bit.B0) typenum.bit.B0)
      typenum.bit.B0) typenum.bit.B0) typenum.bit.B0) typenum.bit.B0)
      typenum.bit.B0) typenum.bit.B0) Clause2_Output)
      (typenummarker_traitsNonZeroInst : typenum.marker_traits.NonZero
      Clause2_Output) :
      (digest.core_api.wrapper.CoreWrapper T Clause0_BufferKind
        Clause0_Clause0_BlockSize Clause0_Clause0_Clause0_ArrayType Clause2_Output)
        → (Slice Std.U8) → Result (digest.core_api.wrapper.CoreWrapper T
        Clause0_BufferKind Clause0_Clause0_BlockSize
        Clause0_Clause0_Clause0_ArrayType Clause2_Output)
  op217 {T : Type} {Clause1_BufferKind : Type} {Clause1_Clause0_BlockSize : Type}
      {Clause1_Clause0_Clause0_ArrayType : Type} {Clause2_Output : Type}
      (coredefaultDefaultInst : core.default.Default T) (BufferKindUserInst :
      digest.core_api.BufferKindUser T Clause1_BufferKind Clause1_Clause0_BlockSize
      Clause1_Clause0_Clause0_ArrayType)
      (typenumtype_operatorsIsLessClause1_Clause0_BlockSizeUIntUIntUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0B0B0Clause2_OutputInst
      : typenum.type_operators.IsLess Clause1_Clause0_BlockSize (typenum.uint.UInt
      (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt
      (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt
      typenum.uint.UTerm typenum.bit.B1) typenum.bit.B0) typenum.bit.B0)
      typenum.bit.B0) typenum.bit.B0) typenum.bit.B0) typenum.bit.B0)
      typenum.bit.B0) typenum.bit.B0) Clause2_Output)
      (typenummarker_traitsNonZeroInst : typenum.marker_traits.NonZero
      Clause2_Output) (coredefaultDefaultInst1 : core.default.Default
      Clause1_Clause0_BlockSize) (coredefaultDefaultInst2 : core.default.Default
      Clause1_BufferKind) :
      Result (digest.core_api.wrapper.CoreWrapper T Clause1_BufferKind
        Clause1_Clause0_BlockSize Clause1_Clause0_Clause0_ArrayType Clause2_Output)
  op218 {T : Type} {OutSize : Type} (O : Type) {Clause0_Clause0_Clause0_BlockSize :
      Type} {Clause0_Clause0_Clause0_Clause0_ArrayType : Type}
      {Clause0_Clause1_OutputSize : Type} {Clause0_Clause1_Clause0_ArrayType :
      Type} {Clause0_Clause2_BufferKind : Type} {Clause0_Clause2_Clause0_BlockSize
      : Type} {Clause0_Clause2_Clause0_Clause0_ArrayType : Type}
      {Clause0_Clause3_Output : Type} {Clause1_ArrayType : Type} {Clause2_Output :
      Type} {Clause4_Output : Type} (VariableOutputCoreInst :
      digest.core_api.VariableOutputCore T Clause0_Clause0_Clause0_BlockSize
      Clause0_Clause0_Clause0_Clause0_ArrayType Clause0_Clause1_OutputSize
      Clause0_Clause1_Clause0_ArrayType Clause0_Clause2_BufferKind
      Clause0_Clause2_Clause0_BlockSize Clause0_Clause2_Clause0_Clause0_ArrayType
      Clause0_Clause3_Output)
      (generic_arrayArrayLengthOutSizeU8Clause1_ArrayTypeInst :
      generic_array.ArrayLength OutSize Std.U8 Clause1_ArrayType)
      (typenumtype_operatorsIsLessOrEqualInst :
      typenum.type_operators.IsLessOrEqual OutSize Clause0_Clause1_OutputSize
      Clause2_Output) (typenummarker_traitsNonZeroInst :
      typenum.marker_traits.NonZero Clause2_Output)
      (typenumtype_operatorsIsLessClause0_Clause0_Clause0_BlockSizeUIntUIntUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0B0B0Clause4_OutputInst
      : typenum.type_operators.IsLess Clause0_Clause0_Clause0_BlockSize
      (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt
      (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt
      (typenum.uint.UInt typenum.uint.UTerm typenum.bit.B1) typenum.bit.B0)
      typenum.bit.B0) typenum.bit.B0) typenum.bit.B0) typenum.bit.B0)
      typenum.bit.B0) typenum.bit.B0) typenum.bit.B0) Clause4_Output)
      (typenummarker_traitsNonZeroInst1 : typenum.marker_traits.NonZero
      Clause4_Output) :
      Result (digest.core_api.ct_variable.CtVariableCoreWrapper T OutSize O
        Clause0_Clause0_Clause0_BlockSize Clause0_Clause0_Clause0_Clause0_ArrayType
        Clause0_Clause1_OutputSize Clause0_Clause1_Clause0_ArrayType
        Clause0_Clause2_BufferKind Clause0_Clause2_Clause0_BlockSize
        Clause0_Clause2_Clause0_Clause0_ArrayType Clause0_Clause3_Output
        Clause1_ArrayType Clause2_Output Clause4_Output)
  op219 {T : Type} {OutSize : Type} {O : Type} {Clause0_Clause0_Clause0_BlockSize :
      Type} {Clause0_Clause0_Clause0_Clause0_ArrayType : Type}
      {Clause0_Clause1_OutputSize : Type} {Clause0_Clause1_Clause0_ArrayType :
      Type} {Clause0_Clause2_BufferKind : Type} {Clause0_Clause2_Clause0_BlockSize
      : Type} {Clause0_Clause2_Clause0_Clause0_ArrayType : Type}
      {Clause0_Clause3_Output : Type} {Clause1_ArrayType : Type} {Clause2_Output :
      Type} {Clause4_Output : Type} (VariableOutputCoreInst :
      digest.core_api.VariableOutputCore T Clause0_Clause0_Clause0_BlockSize
      Clause0_Clause0_Clause0_Clause0_ArrayType Clause0_Clause1_OutputSize
      Clause0_Clause1_Clause0_ArrayType Clause0_Clause2_BufferKind
      Clause0_Clause2_Clause0_BlockSize Clause0_Clause2_Clause0_Clause0_ArrayType
      Clause0_Clause3_Output)
      (generic_arrayArrayLengthOutSizeU8Clause1_ArrayTypeInst :
      generic_array.ArrayLength OutSize Std.U8 Clause1_ArrayType)
      (typenumtype_operatorsIsLessOrEqualInst :
      typenum.type_operators.IsLessOrEqual OutSize Clause0_Clause1_OutputSize
      Clause2_Output) (typenummarker_traitsNonZeroInst :
      typenum.marker_traits.NonZero Clause2_Output)
      (typenumtype_operatorsIsLessClause0_Clause0_Clause0_BlockSizeUIntUIntUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0B0B0Clause4_OutputInst
      : typenum.type_operators.IsLess Clause0_Clause0_Clause0_BlockSize
      (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt
      (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt
      (typenum.uint.UInt typenum.uint.UTerm typenum.bit.B1) typenum.bit.B0)
      typenum.bit.B0) typenum.bit.B0) typenum.bit.B0) typenum.bit.B0)
      typenum.bit.B0) typenum.bit.B0) typenum.bit.B0) Clause4_Output)
      (typenummarker_traitsNonZeroInst1 : typenum.marker_traits.NonZero
      Clause4_Output) :
      (digest.core_api.ct_variable.CtVariableCoreWrapper T OutSize O
        Clause0_Clause0_Clause0_BlockSize Clause0_Clause0_Clause0_Clause0_ArrayType
        Clause0_Clause1_OutputSize Clause0_Clause1_Clause0_ArrayType
        Clause0_Clause2_BufferKind Clause0_Clause2_Clause0_BlockSize
        Clause0_Clause2_Clause0_Clause0_ArrayType Clause0_Clause3_Output
        Clause1_ArrayType Clause2_Output Clause4_Output) →
        (block_buffer.BlockBuffer Clause0_Clause0_Clause0_BlockSize
        Clause0_Clause2_BufferKind Clause0_Clause0_Clause0_Clause0_ArrayType
        Clause4_Output) → (generic_array.GenericArray Std.U8 OutSize
        Clause1_ArrayType) → Result
        ((digest.core_api.ct_variable.CtVariableCoreWrapper T OutSize O
        Clause0_Clause0_Clause0_BlockSize Clause0_Clause0_Clause0_Clause0_ArrayType
        Clause0_Clause1_OutputSize Clause0_Clause1_Clause0_ArrayType
        Clause0_Clause2_BufferKind Clause0_Clause2_Clause0_BlockSize
        Clause0_Clause2_Clause0_Clause0_ArrayType Clause0_Clause3_Output
        Clause1_ArrayType Clause2_Output Clause4_Output) ×
        (block_buffer.BlockBuffer Clause0_Clause0_Clause0_BlockSize
        Clause0_Clause2_BufferKind Clause0_Clause0_Clause0_Clause0_ArrayType
        Clause4_Output) × (generic_array.GenericArray Std.U8 OutSize
        Clause1_ArrayType))
  op220 {T : Type} {OutSize : Type} {O : Type} {Clause0_Clause0_Clause0_BlockSize :
      Type} {Clause0_Clause0_Clause0_Clause0_ArrayType : Type}
      {Clause0_Clause1_OutputSize : Type} {Clause0_Clause1_Clause0_ArrayType :
      Type} {Clause0_Clause2_BufferKind : Type} {Clause0_Clause2_Clause0_BlockSize
      : Type} {Clause0_Clause2_Clause0_Clause0_ArrayType : Type}
      {Clause0_Clause3_Output : Type} {Clause1_ArrayType : Type} {Clause2_Output :
      Type} {Clause4_Output : Type} (VariableOutputCoreInst :
      digest.core_api.VariableOutputCore T Clause0_Clause0_Clause0_BlockSize
      Clause0_Clause0_Clause0_Clause0_ArrayType Clause0_Clause1_OutputSize
      Clause0_Clause1_Clause0_ArrayType Clause0_Clause2_BufferKind
      Clause0_Clause2_Clause0_BlockSize Clause0_Clause2_Clause0_Clause0_ArrayType
      Clause0_Clause3_Output)
      (generic_arrayArrayLengthOutSizeU8Clause1_ArrayTypeInst :
      generic_array.ArrayLength OutSize Std.U8 Clause1_ArrayType)
      (typenumtype_operatorsIsLessOrEqualInst :
      typenum.type_operators.IsLessOrEqual OutSize Clause0_Clause1_OutputSize
      Clause2_Output) (typenummarker_traitsNonZeroInst :
      typenum.marker_traits.NonZero Clause2_Output)
      (typenumtype_operatorsIsLessClause0_Clause0_Clause0_BlockSizeUIntUIntUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0B0B0Clause4_OutputInst
      : typenum.type_operators.IsLess Clause0_Clause0_Clause0_BlockSize
      (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt
      (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt (typenum.uint.UInt
      (typenum.uint.UInt typenum.uint.UTerm typenum.bit.B1) typenum.bit.B0)
      typenum.bit.B0) typenum.bit.B0) typenum.bit.B0) typenum.bit.B0)
      typenum.bit.B0) typenum.bit.B0) typenum.bit.B0) Clause4_Output)
      (typenummarker_traitsNonZeroInst1 : typenum.marker_traits.NonZero
      Clause4_Output) :
      (digest.core_api.ct_variable.CtVariableCoreWrapper T OutSize O
        Clause0_Clause0_Clause0_BlockSize Clause0_Clause0_Clause0_Clause0_ArrayType
        Clause0_Clause1_OutputSize Clause0_Clause1_Clause0_ArrayType
        Clause0_Clause2_BufferKind Clause0_Clause2_Clause0_BlockSize
        Clause0_Clause2_Clause0_Clause0_ArrayType Clause0_Clause3_Output
        Clause1_ArrayType Clause2_Output Clause4_Output) → (Slice
        (generic_array.GenericArray Std.U8 Clause0_Clause0_Clause0_BlockSize
        Clause0_Clause0_Clause0_Clause0_ArrayType)) → Result
        (digest.core_api.ct_variable.CtVariableCoreWrapper T OutSize O
        Clause0_Clause0_Clause0_BlockSize Clause0_Clause0_Clause0_Clause0_ArrayType
        Clause0_Clause1_OutputSize Clause0_Clause1_Clause0_ArrayType
        Clause0_Clause2_BufferKind Clause0_Clause2_Clause0_BlockSize
        Clause0_Clause2_Clause0_Clause0_ArrayType Clause0_Clause3_Output
        Clause1_ArrayType Clause2_Output Clause4_Output)
  op221 : Result block_buffer.Eager
  op222 :
      (Slice aspis_core.field.QM31) → (Array aspis_core.field.QM31 10#usize) →
        Result (Option aspis_core.field.QM31)
  op223 :
      aspis_core.field.M31 → (Slice aspis_core.field.M31) →
        aspis_core.field.QM31 → Result aspis_core.field.QM31
  op224 :
      aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1 → Std.U64
        → aspis_core.field.QM31 → aspis_core.field.QM31 → Result
        (core.result.Result (alloc.vec.Vec aspis_core.field.QM31)
        aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1)
  op225 :
      aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → Result
        aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
  op226 :
      aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → Result
        (core.result.Result (alloc.vec.Vec Std.U8)
        aspis_core.state_only_prefix.r0.Error)
  op227 :
      aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public → (Array
        (Array aspis_core.field.QM31 29#usize) 3#usize) → (Array
        aspis_core.field.QM31 10#usize) →
        aspis_core.state_only_prefix.r0.Challenges → Result (core.result.Result
        aspis_core.field.QM31 aspis_core.state_only_prefix.r0.Error)
  op228 :
      Result (core.result.Result (alloc.vec.Vec
        aspis_statement.pool_v1.pair_trace.PoolV1PairCopyLinkV1)
        aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1)
  op229 :
      aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 →
        aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1
        → Result Bool
  op230 : (Slice aspis_core.field.QM31) → Result (Option aspis_core.field.QM31)
  op231 :
      aspis_statement.state_only_trace.StateOnlyTraceFoundation → Result
        aspis_statement.state_only_trace.StateOnlyTraceFoundation
  op232 :
      aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1PublicChallenges → Result (Bool
        × aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.R1CheckTimes)
  op233 : transport.Variant → transport.Variant → Result Bool
  op234 : transport.Variant → Result Std.U8
  op235 : Result Std.U32
  op236 : Result Std.Usize
  op237 : Result (Array Std.Usize 6#usize)
  op238 : (Array Std.U8 32#usize) → Result (Array Std.U8 32#usize)
  op239 : Result Std.Usize
  op240 : Result Std.Usize
  op241 : Result Std.Usize
  op242 : Result Std.Usize
  op243 : Result Std.Usize
  op244 : Result Std.Usize
  op245 : Result (Array Std.U8 8#usize)
  op246 {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H) :
      H → (Array Std.U8 32#usize) → (Array Std.U8 32#usize) → Result (Array
        Std.U8 32#usize)
  op247 :
      Std.U16 → Std.Usize → aspis_core.field.wide_exact.WideExact → Result
        Unit
  op248 : (Array Std.U8 32#usize) → Result aspis_core.field.QM31
  op249 : (Array Std.U8 32#usize) → Result aspis_core.field.wide_exact.WideExact
  op250 : (Array Std.U8 32#usize) → Result aspis_core.field.wide_exact.WideExact
  op251 :
      weights.Weights → aspis_core.field.wide_exact.WideExact → Result
        (core.result.Result (alloc.vec.Vec aspis_core.field.wide_exact.WideExact)
        verifier.Error)
  op252 :
      transport.Variant → (Array aspis_core.field.QM31 10#usize) → (Array
        aspis_core.circle.SecureCirclePoint 2#usize) → Result (core.result.Result
        weights.Weights verifier.Error)
  op253 :
      weights.Weights → Std.Usize → Std.Usize → Result aspis_core.field.QM31
  op254 (N : Std.Usize) :
      aspis_core.field.wide_exact.WideExact → Result (Array
        aspis_core.field.wide_exact.WideExact N)
  op255 {T : Type} (coremarkerCopyInst : core.marker.Copy T) :
      transport.Variant → (Array T 1024#usize) → Result (Array T 1024#usize)
  op256 : r1_wire.Error → r1_wire.Error → Result Bool
  op257 {T : Type} {F : Type} (coreopsfunctionFnFTupleUsizeTInst :
      core.ops.function.Fn F Std.Usize T) :
      Std.Usize → Std.Usize → F → Result (alloc.vec.Vec T)
  op258 :
      (Slice (Array (Array aspis_core.field.QM31 2#usize) 2#usize)) → (Array
        Std.U16 64#usize) → aspis_core.field.QM31 → Result Bool
  op259 :
      (Array Std.U8 32#usize) → aspis_core.r0_transcript.CircleRow → Result
        aspis_core.circle.SecureCirclePoint
  op260 : Result (Slice Std.U8)
  op261 : std.fs.File → Slice Std.U8 → Result ((core.result.Result Unit std.io.error.Error) × std.fs.File)

abbrev Shared0T.Insts.CoreConvertAsRef.as_ref [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op0 types ext
abbrev Slice.Insts.CoreConvertAsRefSlice.as_ref [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op1 types ext
abbrev core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op2 types ext
abbrev core.mem.take [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op3 types ext
abbrev core.mem.drop [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op4 types ext
abbrev core.option.Option.is_some_and [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op5 types ext
abbrev core.option.Option.as_ref [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op6 types ext
abbrev core.option.Option.ok_or [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op7 types ext
abbrev core.option.Option.Insts.CoreCmpPartialEqOption.eq [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op8 types ext
abbrev core.option.Option.Insts.CoreOpsTry_traitTry.branch [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op9 types ext
abbrev core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op10 types ext
abbrev core.result.Result.map [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op11 types ext
abbrev core.result.Result.map_err [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op12 types ext
abbrev core.sync.atomic.compiler_fence [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op13 types ext
abbrev std.fs.File.open [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op14 types ext
abbrev std.fs.File.sync_all [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op15 types ext
abbrev std.io.Write.write_all.default [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op16 types ext
abbrev std.fs.File.Insts.StdIoWrite.flush [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op17 types ext
abbrev std.fs.File.Insts.StdIoWrite.write [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op18 types ext
abbrev std.fs.OpenOptions.new [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op19 types ext
abbrev std.fs.OpenOptions.write [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op20 types ext
abbrev std.fs.OpenOptions.create_new [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op21 types ext
abbrev std.fs.OpenOptions.open [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op22 types ext
abbrev std.io.error.Error.kind [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op23 types ext
abbrev std.fs.OpenOptions.Insts.StdOsUnixFsOpenOptionsExt.mode [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op24 types ext
abbrev std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op25 types ext
abbrev std.path.Path.join [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op26 types ext
abbrev std.path.Path.Insts.CoreConvertAsRefPath.as_ref [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op27 types ext
abbrev alloc.string.String.Insts.CoreConvertAsRefPath.as_ref [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op28 types ext
abbrev std.path.PathBuf.Insts.CoreConvertAsRefPath.as_ref [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op29 types ext
abbrev alloc.string.String.with_capacity [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op30 types ext
abbrev alloc.string.String.push_str [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op31 types ext
abbrev alloc.vec.Vec.try_reserve_exact [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op32 types ext
abbrev alloc.vec.Vec.pop [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op33 types ext
abbrev alloc.vec.Vec.is_empty [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op34 types ext
abbrev alloc.vec.Vec.Insts.CoreDefaultDefault.default [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op35 types ext
abbrev Array.Insts.CoreConvertTryFromVecVec.try_from [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op36 types ext
abbrev aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op37 types ext
abbrev aspis_core.digest.LegacyHashFn.Insts.CoreCloneClone.clone [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op38 types ext
abbrev aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32.digest [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op39 types ext
abbrev aspis_core.field.wide_exact.WideExact.Insts.CoreCloneClone.clone [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op40 types ext
abbrev aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.eq [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op41 types ext
abbrev aspis_core.field.wide_exact.WideExact.ZERO [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op42 types ext
abbrev aspis_core.field.wide_exact.WideExact.impl.c0 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op43 types ext
abbrev aspis_core.field.wide_exact.WideExact.impl.c1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op44 types ext
abbrev aspis_core.field.wide_exact.WideExact.from_qm31 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op45 types ext
abbrev aspis_core.field.wide_exact.WideExact.add [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op46 types ext
abbrev aspis_core.field.wide_exact.WideExact.mul [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op47 types ext
abbrev aspis_core.field.wide_exact.WideExact.mul_qm31 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op48 types ext
abbrev aspis_core.field.wide_exact.WideExact.to_limbs [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op49 types ext
abbrev aspis_core.field.wide_exact.WideExact.from_le_bytes [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op50 types ext
abbrev aspis_core.field.wide_exact.WideExact.to_le_bytes [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op51 types ext
abbrev aspis_core.field.wide_exact.WideExact.mul_m31 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op52 types ext
abbrev aspis_core.field.M31.Insts.CoreCloneClone.clone [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op53 types ext
abbrev aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op54 types ext
abbrev aspis_core.field.M31.ZERO [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op55 types ext
abbrev aspis_core.field.M31.ONE [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op56 types ext
abbrev aspis_core.field.M31.mul [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op57 types ext
abbrev aspis_core.field.M31.double [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op58 types ext
abbrev aspis_core.field.M31.inv [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op59 types ext
abbrev aspis_core.field.CM31.new [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op60 types ext
abbrev aspis_core.field.CM31.from_m31 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op61 types ext
abbrev aspis_core.field.QM31.Insts.CoreCloneClone.clone [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op62 types ext
abbrev aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op63 types ext
abbrev aspis_core.field.QM31.ZERO [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op64 types ext
abbrev aspis_core.field.QM31.ONE [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op65 types ext
abbrev aspis_core.field.QM31.from_cm31 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op66 types ext
abbrev aspis_core.field.QM31.add [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op67 types ext
abbrev aspis_core.field.QM31.sub [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op68 types ext
abbrev aspis_core.field.QM31.mul [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op69 types ext
abbrev aspis_core.field.QM31.mul_m31 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op70 types ext
abbrev aspis_core.field.QM31.from_le_bytes [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op71 types ext
abbrev aspis_core.field.QM31.write_le_bytes [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op72 types ext
abbrev aspis_core.field.M31.add [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op73 types ext
abbrev aspis_core.field.M31.sub [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op74 types ext
abbrev aspis_core.r0.domain.FibreIndex.new [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op75 types ext
abbrev aspis_core.r0.domain.FibreIndex.get [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op76 types ext
abbrev aspis_core.r0.domain.Point.Insts.CoreCloneClone.clone [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op77 types ext
abbrev aspis_core.r0.domain.fibre_point [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op78 types ext
abbrev aspis_core.r0.encoder.eval_message [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op79 types ext
abbrev aspis_core.r0.fold.phi_inverse [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op80 types ext
abbrev aspis_core.r0.heap.filled [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op81 types ext
abbrev aspis_core.r0.merkle.C1_TAG [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op82 types ext
abbrev aspis_core.r0.merkle.C2_TAG [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op83 types ext
abbrev aspis_core.r0.merkle.leaf [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op84 types ext
abbrev aspis_core.r0.Error.Insts.CoreFmtDebug.fmt [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op85 types ext
abbrev aspis_core.r0.opening.LANES [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op86 types ext
abbrev aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.ZERO [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op87 types ext
abbrev aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.ZERO [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op88 types ext
abbrev aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.ZERO [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op89 types ext
abbrev aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.ONE [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op90 types ext
abbrev aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.ONE [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op91 types ext
abbrev aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.ONE [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op92 types ext
abbrev aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.add [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op93 types ext
abbrev aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.add [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op94 types ext
abbrev aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.add [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op95 types ext
abbrev aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.sub [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op96 types ext
abbrev aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.sub [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op97 types ext
abbrev aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.sub [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op98 types ext
abbrev aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.neg [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op99 types ext
abbrev aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.neg [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op100 types ext
abbrev aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.neg [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op101 types ext
abbrev aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.mul [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op102 types ext
abbrev aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.mul [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op103 types ext
abbrev aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.mul [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op104 types ext
abbrev aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.try_inv [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op105 types ext
abbrev aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.from_m31 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op106 types ext
abbrev aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.try_inv [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op107 types ext
abbrev aspis_core.field.QM31.Insts.Aspis_coreR0ScalarCodeField.from_m31 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op108 types ext
abbrev aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.try_inv [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op109 types ext
abbrev aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op110 types ext
abbrev aspis_core.state_only_hiding.PINNED_POOL_V1_PAYMENT_RELATION_FREE_MASK_FINGERPRINT [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op111 types ext
abbrev aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op112 types ext
abbrev aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op113 types ext
abbrev aspis_core.state_only_hiding.StateOnlyHidingContext.Insts.CoreCmpPartialEqStateOnlyHidingContext.eq [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op114 types ext
abbrev aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op115 types ext
abbrev aspis_core.state_only_hiding.StateOnlyHidingContext.encode [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op116 types ext
abbrev aspis_core.state_only_hiding.state_only_selected_mask_value [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op117 types ext
abbrev aspis_core.state_only_prefix.r0.statement_points [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op118 types ext
abbrev aspis_core.state_only_private_merkle.private_leaf_hash [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op119 types ext
abbrev aspis_core.state_only_sumcheck.state_only_boundary_sum [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op120 types ext
abbrev aspis_core.state_only_sumcheck.evaluate_state_only_polynomial [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op121 types ext
abbrev Array.Insts.ZeroizeZeroize.zeroize [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op122 types ext
abbrev zeroize.Zeroize.Blanket.zeroize [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op123 types ext
abbrev aspis_prover.state_only_hiding.volatile_clear_cell [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op124 types ext
abbrev zeroize.Zeroizing.Insts.CoreConvertAsMut.as_mut [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op125 types ext
abbrev zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op126 types ext
abbrev zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op127 types ext
abbrev zeroize.Zeroizing.new [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op128 types ext
abbrev getrandom.fill [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op129 types ext
abbrev zeroize.Zeroizing.Insts.ZeroizeZeroize.zeroize [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op130 types ext
abbrev zeroize.Zeroizing.Insts.CoreConvertAsRef.as_ref [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op131 types ext
abbrev aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_relation_free_mask_cells_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op132 types ext
abbrev aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_rows_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op133 types ext
abbrev aspis_statement.pool_v1.pair_forest_hiding.pool_v1_pair_forest_copy_active_row_masks_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op134 types ext
abbrev typenum.uint.UTerm.Insts.TypenumPrivatePrivateCmpUTermSoFarSoFar.private_cmp [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op135 types ext
abbrev typenum.uint.UTerm.Insts.TypenumPrivatePrivateCmpUIntSoFarLess.private_cmp [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op136 types ext
abbrev typenum.uint.UIntUlB1.Insts.TypenumPrivatePrivateCmpUIntUrB0SoFarClause3_Output.private_cmp [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op137 types ext
abbrev typenum.uint.UIntUlB1.Insts.TypenumPrivatePrivateCmpUIntUrB1SoFarClause3_Output.private_cmp [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op138 types ext
abbrev typenum.uint.UIntUlB0.Insts.TypenumPrivatePrivateCmpUIntUrB0SoFarClause3_Output.private_cmp [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op139 types ext
abbrev typenum.uint.UIntUlB0.Insts.TypenumType_operatorsCmpUIntUrB0Clause2_Output.compare [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op140 types ext
abbrev typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_isize [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op141 types ext
abbrev typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i64 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op142 types ext
abbrev typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i32 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op143 types ext
abbrev typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i16 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op144 types ext
abbrev typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_i8 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op145 types ext
abbrev typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_usize [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op146 types ext
abbrev typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u64 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op147 types ext
abbrev typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u32 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op148 types ext
abbrev typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u16 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op149 types ext
abbrev typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.to_u8 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op150 types ext
abbrev typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.ISIZE [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op151 types ext
abbrev typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I64 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op152 types ext
abbrev typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I32 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op153 types ext
abbrev typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I16 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op154 types ext
abbrev typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.I8 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op155 types ext
abbrev typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.USIZE [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op156 types ext
abbrev typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U64 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op157 types ext
abbrev typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U32 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op158 types ext
abbrev typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U16 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op159 types ext
abbrev typenum.uint.UInt.Insts.TypenumMarker_traitsUnsigned.U8 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op160 types ext
abbrev typenum.uint.UInt.Insts.CoreDefaultDefault.default [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op161 types ext
abbrev typenum.uint.UInt.Insts.CoreCloneClone.clone [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op162 types ext
abbrev typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_isize [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op163 types ext
abbrev typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i64 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op164 types ext
abbrev typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i32 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op165 types ext
abbrev typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i16 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op166 types ext
abbrev typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_i8 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op167 types ext
abbrev typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_usize [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op168 types ext
abbrev typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u64 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op169 types ext
abbrev typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u32 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op170 types ext
abbrev typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u16 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op171 types ext
abbrev typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.to_u8 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op172 types ext
abbrev typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.ISIZE [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op173 types ext
abbrev typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I64 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op174 types ext
abbrev typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I32 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op175 types ext
abbrev typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I16 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op176 types ext
abbrev typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.I8 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op177 types ext
abbrev typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.USIZE [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op178 types ext
abbrev typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U64 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op179 types ext
abbrev typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U32 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op180 types ext
abbrev typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U16 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op181 types ext
abbrev typenum.uint.UTerm.Insts.TypenumMarker_traitsUnsigned.U8 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op182 types ext
abbrev typenum.uint.UTerm.Insts.CoreDefaultDefault.default [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op183 types ext
abbrev typenum.uint.UTerm.Insts.CoreCloneClone.clone [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op184 types ext
abbrev typenum.type_operators.IsLessOrEqual.Blanket.is_less_or_equal [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op185 types ext
abbrev typenum.type_operators.IsLess.Blanket.is_less [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op186 types ext
abbrev typenum.private.IsLessOrEqualPrivateABEqualB1.Blanket.is_less_or_equal_private [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op187 types ext
abbrev typenum.bit.B1.Insts.TypenumMarker_traitsBit.to_bool [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op188 types ext
abbrev typenum.bit.B1.Insts.TypenumMarker_traitsBit.to_u8 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op189 types ext
abbrev typenum.bit.B1.Insts.TypenumMarker_traitsBit.new [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op190 types ext
abbrev typenum.bit.B1.Insts.TypenumMarker_traitsBit.BOOL [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op191 types ext
abbrev typenum.bit.B1.Insts.TypenumMarker_traitsBit.U8 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op192 types ext
abbrev typenum.bit.B1.Insts.CoreDefaultDefault.default [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op193 types ext
abbrev typenum.bit.B1.Insts.CoreCloneClone.clone [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op194 types ext
abbrev typenum.private.IsLessPrivateABLessB1.Blanket.is_less_private [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op195 types ext
abbrev typenum.Equal.Insts.TypenumMarker_traitsOrd.to_ordering [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op196 types ext
abbrev typenum.Greater.Insts.TypenumMarker_traitsOrd.to_ordering [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op197 types ext
abbrev typenum.bit.B0.Insts.TypenumMarker_traitsBit.to_bool [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op198 types ext
abbrev typenum.bit.B0.Insts.TypenumMarker_traitsBit.to_u8 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op199 types ext
abbrev typenum.bit.B0.Insts.TypenumMarker_traitsBit.new [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op200 types ext
abbrev typenum.bit.B0.Insts.TypenumMarker_traitsBit.BOOL [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op201 types ext
abbrev typenum.bit.B0.Insts.TypenumMarker_traitsBit.U8 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op202 types ext
abbrev typenum.bit.B0.Insts.CoreDefaultDefault.default [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op203 types ext
abbrev typenum.bit.B0.Insts.CoreCloneClone.clone [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op204 types ext
abbrev sha2.core_api.Sha256VarCore.Insts.DigestCore_apiVariableOutputCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80EagerUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80B1.finalize_variable_core [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op205 types ext
abbrev sha2.core_api.Sha256VarCore.Insts.DigestCore_apiVariableOutputCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80EagerUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80B1.new [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op206 types ext
abbrev sha2.core_api.Sha256VarCore.Insts.DigestCore_apiVariableOutputCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80UIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80EagerUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80B1.TRUNC_SIDE [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op207 types ext
abbrev sha2.core_api.Sha256VarCore.Insts.DigestCore_apiUpdateCoreUIntUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0B0GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplEvenU8GenericArrayImplOddU8ArrayU80.update_blocks [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op208 types ext
abbrev block_buffer.Eager.Insts.Block_bufferSealedSealed.split_blocks [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op209 types ext
abbrev block_buffer.Eager.Insts.Block_bufferSealedSealed.invariant [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op210 types ext
abbrev ArrayT32.Insts.CoreConvertFromGenericArrayTUIntUIntUIntUIntUIntUIntUTermB1B0B0B0B0B0GenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplEvenTGenericArrayImplOddTArrayT0.from [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op211 types ext
abbrev digest.digest.Digest.Blanket.finalize [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op212 types ext
abbrev digest.digest.Digest.Blanket.update [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op213 types ext
abbrev digest.digest.Digest.Blanket.new [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op214 types ext
abbrev digest.core_api.wrapper.CoreWrapper.Insts.DigestFixedOutput.finalize_into [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op215 types ext
abbrev digest.core_api.wrapper.CoreWrapper.Insts.DigestUpdate.update [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op216 types ext
abbrev digest.core_api.wrapper.CoreWrapper.Insts.CoreDefaultDefault.default [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op217 types ext
abbrev digest.core_api.ct_variable.CtVariableCoreWrapper.Insts.CoreDefaultDefault.default [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op218 types ext
abbrev digest.core_api.ct_variable.CtVariableCoreWrapper.Insts.DigestCore_apiFixedOutputCore.finalize_fixed_core [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op219 types ext
abbrev digest.core_api.ct_variable.CtVariableCoreWrapper.Insts.DigestCore_apiUpdateCore.update_blocks [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op220 types ext
abbrev block_buffer.Eager.Insts.CoreDefaultDefault.default [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op221 types ext
abbrev aspis_statement.constraints_v4.multilinear_evaluate_qm31 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op222 types ext
abbrev aspis_statement.logup.compress_tagged_tuple [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op223 types ext
abbrev aspis_statement.pool_v1.pair_forest_semantic_oracle.build_pool_v1_pair_forest_copy_helper_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op224 types ext
abbrev aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.transition [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op225 types ext
abbrev aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op226 types ext
abbrev aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op227 types ext
abbrev aspis_statement.pool_v1.pair_forest_trace.build_pool_v1_pair_forest_copy_registry_v1 [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op228 types ext
abbrev aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1.Insts.CoreCmpPartialEqPoolV1PairLatePublicStatementV1.eq [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op229 types ext
abbrev aspis_statement.state_only_semantic.state_only_copy_helper_sum [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op230 types ext
abbrev aspis_statement.state_only_trace.StateOnlyTraceFoundation.Insts.CoreCloneClone.clone [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op231 types ext
abbrev aspis_z4b_probe.probe.z9.z9b.z9c.z9d.z9e.p_r1_check [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op232 types ext
abbrev transport.Variant.Insts.CoreCmpPartialEqVariant.eq [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op233 types ext
abbrev transport.Variant.tag [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op234 types ext
abbrev multiproof.LEAF_BITS [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op235 types ext
abbrev multiproof.MAX_BATCH [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op236 types ext
abbrev compact.SLOT_NODES [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op237 types ext
abbrev host_commitment.clear_private_salt [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op238 types ext
abbrev r1_wire.CLAIMS [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op239 types ext
abbrev r1_wire.LANES [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op240 types ext
abbrev compact.LOGICAL_SEMANTIC [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op241 types ext
abbrev compact.PROOF_BYTES [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op242 types ext
abbrev compact.OFF_NODES [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op243 types ext
abbrev compact.OFF_OPENINGS [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op244 types ext
abbrev compact.MAGIC [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op245 types ext
abbrev multiproof.binary_parent [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op246 types ext
abbrev trace.value [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op247 types ext
abbrev sampler.qm31_sample [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op248 types ext
abbrev sampler.gamma_sample [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op249 types ext
abbrev sampler.ordinary_sample [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op250 types ext
abbrev weights.Weights.materialize [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op251 types ext
abbrev weights.Weights.new [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op252 types ext
abbrev weights.Weights.raw [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op253 types ext
abbrev weights.powers [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op254 types ext
abbrev transport.Variant.coefficients [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op255 types ext
abbrev r1_wire.Error.Insts.CoreCmpPartialEqError.eq [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op256 types ext
abbrev host_work.map [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op257 types ext
abbrev ct_pole.all_slots_clear [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op258 types ext
abbrev sampler.circle_sample [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op259 types ext
abbrev r1_wire.DOMAIN [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op260 types ext
abbrev std.fs.File.Insts.StdIoWrite.write_all [types : ExternalTypes] [ext : ExternalFuns] := @ExternalFuns.op261 types ext

end ProverRwFull
