# JointFunctionalBinding focused Lean receipt

`lean/JointFunctionalBinding.lean` proves direct two-challenge binding for the
specified six linear functionals over 29 tuple entries. The first bad set is
over `ts × Fin 6`, with degree bound 28 and cardinality bound 16,800. The
second bad set is over `ts`, with degree bound 6 and cardinality bound 600.
The proof derives the delta-polynomial coefficients, the kappa-polynomial
coefficients, and the weighted discrepancy identity in the file itself. The
candidate family, tuple, functionals, and claims are fixed parameters to the
bad sets. This is a deterministic algebra/root-counting lemma; it makes no
Fiat--Shamir, source-extraction, uniqueness, or security claim.

Successful source SHA-256:
`9a63100ea4e301a813c001beee84e5b4938748d8c429901f1668f6b54f344a19`.
The focused target was `R1JointFunctionalBinding`, using:

```sh
./run2.sh joint-functional-binding-r1-20261013h R1JointFunctionalBinding 5000 6
```

The pinned NUC runner reported populated reservations of 24 GiB plus the
6 GiB scope. Scope properties were `MemoryHigh=4G`, `MemoryMax=6G`, and
`MemorySwapMax=0`; Lean memory limit was 5000 MiB. The run exited 0 in
1.76 seconds, peak RSS was 2,099,796 KiB, and swap was zero. The cached module
SHA-256 is `9845a9bf92815a6de7f98331f18cb0eca95586a85bb35d46fc6c801c02365c83`.
All three printed axiom sets were `[propext, Classical.choice, Quot.sound]`,
with no `sorryAx`.

The imported `R1FunctionalBatchClean` source SHA is
`b21ac7058403ffaa617b3d1507a54c5de09767be5c664fd3e16ad619327fad7d`; its
cached `.olean` SHA is
`70e8f4c19f7bdb6d1988ddbee6cd3c626b65d4cec19b3febabd09da91db717cb`. The
environment manifest SHA is
`ad7b87bbcfd84dc762927729c3d35a1822a530e57538a58c9d559f6ec4b6754e`, Lean
revision is `8c9756b28d64dab099da31a4c09229a9e6a2ef35`, and local base revision
was `a29d480477dd7ad3e2d2343f71baa2b4ef91a3df` plus this uncommitted source.

Earlier focused attempts `a` through `g` failed during import or proof
plumbing. Their exact output, `/usr/bin/time -v` logs, and source hashes are
preserved under `remote-evidence/evidence/`; no failed result is omitted. The
successful source snapshot, cached module, and successful run receipts are
also preserved there.
