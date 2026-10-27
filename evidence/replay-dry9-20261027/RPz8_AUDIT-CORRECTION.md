# Audit query syntax correction

RPz8_658 / RPz8_AuditBatch01 fails at line 117:149 with `unexpected token ')'; expected ']'`. The DECL JSON expression had one extra closing parenthesis after axs.map Name.toString. Full original source, receipt and stdout are retained unchanged. No original closure vertex fails and there are zero blocked source descendants.

The query template is corrected, and partition 01 is compiled under the new RPz8_AuditBatch01Fixed module with changed source bytes. Subsequent, previously unattempted partitions use the corrected expression. No proved source, launcher, monitor, source theorem statement or resource cap changes. No unchanged failed input is retried. This adds one compiler attempt to the budget; it is a syntax failure, not a timeout/memory kill or a failed security theorem.
