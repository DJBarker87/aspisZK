import Port8EFF_Bodies
import Port8EFF_Budget
import Port8EFF_CheckpointCode
import Port8EFF_CheckpointEffects
import Port8EFF_Control
import Port8EFF_Driver
import Port8EFF_NativeReader
import Port8EFF_PowersTail
import Port8EFF_ReaderJoin
import Port8EFF_ReaderSkeleton
set_option autoImplicit false

#check @AspisR1.Port8EFF_Bodies.reader_value
#print axioms AspisR1.Port8EFF_Bodies.reader_value

#check @AspisR1.Port8EFF_Bodies.writer_value
#print axioms AspisR1.Port8EFF_Bodies.writer_value

#check @AspisR1.Port8EFF_Bodies.reader_effects
#print axioms AspisR1.Port8EFF_Bodies.reader_effects

#check @AspisR1.Port8EFF_Bodies.writer_effects
#print axioms AspisR1.Port8EFF_Bodies.writer_effects

#check @AspisR1.Port8EFF_Bodies.installed_reader
#print axioms AspisR1.Port8EFF_Bodies.installed_reader

#check @AspisR1.Port8EFF_Bodies.installed_writer
#print axioms AspisR1.Port8EFF_Bodies.installed_writer

#check @AspisR1.Port8EFF_Budget.count
#print axioms AspisR1.Port8EFF_Budget.count

#check @AspisR1.Port8EFF_Budget.reader_bounded
#print axioms AspisR1.Port8EFF_Budget.reader_bounded

#check @AspisR1.Port8EFF_Budget.reader_count
#print axioms AspisR1.Port8EFF_Budget.reader_count

#check @AspisR1.Port8EFF_CheckpointCode.value
#print axioms AspisR1.Port8EFF_CheckpointCode.value

#check @AspisR1.Port8EFF_CheckpointCode.effects
#print axioms AspisR1.Port8EFF_CheckpointCode.effects

#check @AspisR1.Port8EFF_CheckpointEffects.mapped
#print axioms AspisR1.Port8EFF_CheckpointEffects.mapped

#check @AspisR1.Port8EFF_CheckpointEffects.reader
#print axioms AspisR1.Port8EFF_CheckpointEffects.reader

#check @AspisR1.Port8EFF_Control.common_ok
#print axioms AspisR1.Port8EFF_Control.common_ok

#check @AspisR1.Port8EFF_Control.common_source
#print axioms AspisR1.Port8EFF_Control.common_source

#check @AspisR1.Port8EFF_Control.rejected
#print axioms AspisR1.Port8EFF_Control.rejected

#check @AspisR1.Port8EFF_Driver.head
#print axioms AspisR1.Port8EFF_Driver.head

#check @AspisR1.Port8EFF_Driver.common_shape
#print axioms AspisR1.Port8EFF_Driver.common_shape

#check @AspisR1.Port8EFF_Driver.common_reader
#print axioms AspisR1.Port8EFF_Driver.common_reader

#check @AspisR1.Port8EFF_Driver.authenticated_common
#print axioms AspisR1.Port8EFF_Driver.authenticated_common

#check @AspisR1.Port8EFF_Driver.powers_reached
#print axioms AspisR1.Port8EFF_Driver.powers_reached

#check @AspisR1.Port8EFF_Driver.first_reader
#print axioms AspisR1.Port8EFF_Driver.first_reader

#check @AspisR1.Port8EFF_NativeReader.source
#print axioms AspisR1.Port8EFF_NativeReader.source

#check @AspisR1.Port8EFF_ReaderJoin.tail
#print axioms AspisR1.Port8EFF_ReaderJoin.tail

#check @AspisR1.Port8EFF_ReaderJoin.program
#print axioms AspisR1.Port8EFF_ReaderJoin.program

#check @AspisR1.Port8EFF_ReaderSkeleton.native
#print axioms AspisR1.Port8EFF_ReaderSkeleton.native

#check @AspisR1.Port8EFF_ReaderSkeleton.retained
#print axioms AspisR1.Port8EFF_ReaderSkeleton.retained

#print AspisR1.CheckpointBytes5Inputs.Oracle
#print AspisR1.Port8EFF_Bodies.body
#print AspisR1.Port8EFF_Bodies.implementation
