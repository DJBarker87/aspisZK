# Parser pilot obligations

|Function|Native contract|Reference extraction equality|Domain|
|---|---|---|---|
|row_shape|pending|pending|all u8|
|validate_record_fields|pending; existing LPl bridge reused only within its scope|pending|payload length ≤3712|
|parse_record|pending|pending|all row bytes, bounded records|
|parse_record_at|pending|pending|row<27; nonoverflowing offset+record length|
|Prefix::record|pending|pending|arbitrary valid Prefix carrier|
|Prefix::payload|pending|no direct cohort counterpart; compose record/slice|valid framed records|
|expand_values|pending; existing LPn bridge not a contract|pending|source≤1856, destination≤3712|
|compact_row/slot_offset/expand_semantic|pending|pending|caller-established row/buffer bounds|
|Prefix::parse/validated_record; ValidatedRecord::row/framed|pending|pending|actual parsed token|
