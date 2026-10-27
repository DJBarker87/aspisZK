# Stage 2: whole byte parser and checked lane field

XSa_ParserFixed.fixed: identical canonicality decision and SAME packed value on32-byte arrays. XSa_ParserTotal.bytes: full Option/Result association for arbitrary slices, including wrong length and noncanonical inputs. XSa_ParserRange.range: actual checked slice equals raw range, all bounds/errors retained. XSa_ParserLane.lane: complete field equality for each lane0..28 with checked usize multiplication/addition and unwrap; both failure paths retained. Only standard axioms. Every accepted source is new and XSa-prefixed.

Accepted L006/L008/L009/L012. L004/L005/L007/L010/L011 are excluded failed tactic/elaboration snapshots, with corrected forms compiled later; no resource failure or cap increase. Exact #print axioms and resources in receipts. No cached-claim/A2 or native prepared_claim/A3 closure and no headline premise delta.
