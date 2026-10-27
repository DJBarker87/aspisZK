# LPm installed stubs

| Replacement | Target | Domain | Paired Lean theorem | Native stage |
|---|---|---|---|---|
| LPi_contracts::qbytes (unchanged inherited bytes) | QM31::write_le_bytes | Every four raw U32 limbs; exact 16-byte mutable slice | AspisR1.LPi_WriterValues.qm_writer (LPm_L001 unchanged dependency replay) | LPm_K003 PASS; LPm_K002 timeout (excluded) |

The replacement chooses nondeterministic bytes and constrains every byte to the natural little-endian words. It asserts passed slice length 16. Native put_k allocates that exact buffer. This job installs no field multiplication replacement. The inherited module contains unused definitions; their presence is not claimed as native evidence. LPi_STUBS.md retains every inherited pairing and its qualification.
