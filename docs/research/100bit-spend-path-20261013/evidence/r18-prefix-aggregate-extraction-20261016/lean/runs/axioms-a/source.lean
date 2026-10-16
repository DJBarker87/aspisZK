import AspisR1PrefixAggregateParser.Funs

-- Reachable parser/field declarations: standard-only axioms required.
#print axioms AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_limbs
#print axioms AspisR1PrefixAggregateParser.field.wide_exact.WideExact.from_le_bytes
#print axioms AspisR1PrefixAggregateParser.field.QM31.Insts.CoreCmpPartialEqQM31.eq
#print axioms AspisR1PrefixAggregateParser.r1_wire.row_shape
#print axioms AspisR1PrefixAggregateParser.r1_wire.validate_record_fields_loop
#print axioms AspisR1PrefixAggregateParser.r1_wire.validate_record_fields
#print axioms AspisR1PrefixAggregateParser.r1_wire.parse_record
#print axioms AspisR1PrefixAggregateParser.r1_wire.ValidatedRecord.impl.row
#print axioms AspisR1PrefixAggregateParser.r1_wire.ValidatedRecord.impl.framed
#print axioms AspisR1PrefixAggregateParser.r1_wire.ValidatedRecord.payload
#print axioms AspisR1PrefixAggregateParser.r1_wire.parse_record_at
#print axioms AspisR1PrefixAggregateParser.r1_wire.Prefix.parse
#print axioms AspisR1PrefixAggregateParser.r1_wire.Prefix.record
#print axioms AspisR1PrefixAggregateParser.r1_wire.Prefix.payload
#print axioms AspisR1PrefixAggregateParser.r1_wire.Prefix.validated_record

-- Retained unused derived Debug code is reported separately, not a parser premise.
#print axioms AspisR1PrefixAggregateParser.r1_wire.Error.Insts.CoreFmtDebug.fmt
