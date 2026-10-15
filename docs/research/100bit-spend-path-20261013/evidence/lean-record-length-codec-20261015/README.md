# Record length codec evidence

The focused target proves two four-byte codec identities. Under `n < 2^32`, `PublicInitFrame.lengthBytes n` equals the list form of `RetainedFieldByteCodec.encodeWordLE`; and a `WordBytes` value decodes to `n` exactly when its list form equals `lengthBytes n`.

The final NUC compile is attempt `record-length-codec-f`: exit 0, 1.71 s, 3,321,020 KiB peak RSS, zero swap, `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`. Both theorem audits report only `propext`, `Classical.choice`, and `Quot.sound`.

Attempts a–e are retained exact failed drafts, including attempts at the optional list-framing parser equality. That parser equality is not a theorem in this module.
