# The soundness theorem

Soundness means that a false spend is not accepted. This page gives the formal
statement of that property for Aspis, as Lean checked it, and explains how to
read it. The statement covers a whole spend as the verifier on chain carries it
out: the first transaction, which runs the opening stage of the proof and writes
a checkpoint, the second, which picks up the checkpoint, finishes the
verification and settles through the pool, and the handling of the checkpoint
between the two.

It comes as two Lean theorems, one building on the other.

The first theorem, `deployed_splitB`, is about a single run of that spend with
the hash function fixed. It says that if an attacker gets both transactions
accepted, then either the run behaves as the security statement requires, or
the hash queries recorded during the attacker's own run contain a collision of
a kind whose probability is already counted in the bound. The second theorem,
`deployed_charge`, averages over the hash function, which is modelled as a
random oracle. It shows that, oracle by oracle, every accepted run that breaks
the security statement lies in that collision event, and that the event has probability at most total(Q)
for an attacker making Q hash queries, where total(Q) is a function given below
that is about (Q+34)·2^-105.09.

The attacker is arbitrary. It may query the oracle as often as it likes before
choosing the first transaction, see the result, and query again before choosing
the second, and nothing restricts how it uses what it has seen. An accepted
false spend is a run in which both transactions are accepted but the
knowledge extractor, reading the attacker's hash queries, cannot recover a
witness for the spend. How the extracted witness is tied to the spend relation
is to be confirmed by the final audit of the statement, and until then the
theorem should not be read as saying that acceptance implies a valid spend
witness.

Both theorems are proved in Lean with only its three standard axioms. They are
mathematics about the model of the spend path and about the Lean translation of
the frozen Rust source, and several items still stand between them and the
release claim that the deployed version has 100-bit soundness. The most
substantial are tying every committed Lean translation to a fresh translation
of the frozen source, a handful of review items on the bridge between the
checked arithmetic of the translations and the wrapping arithmetic of the
deployed binary, and the treatment of the pool, whose actions the theorem's
game takes as given instead of bringing them inside the proof. These and the
smaller remaining items, with current figures, are in
[`OPEN-GATES.md`](OPEN-GATES.md).

## The first theorem

Lean prints the statement of `deployed_splitB` as follows.

```
@AspisR1.TAS_FinalB.deployed_splitB : ∀ {W Tx : Type}
  (L0 : AspisR1.S2Trust.Library W (Nat → AspisR1.S2W_D189Entry.Record))
  (borrow : @AspisR1.S2Trust.S2TrustedSdkBorrow W (Nat → AspisR1.S2W_D189Entry.Record) L0)
  (copy :
    AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record) →
      Nat → AspisR1.S2Trust.Payload → AspisR1.S2W_TrustedStd.Outcome (Nat → AspisR1.S2W_D189Entry.Record))
  (std : @AspisR1.S2W_TrustedStd.TrustedStd (Nat → AspisR1.S2W_D189Entry.Record) copy)
  (allocation217 : RSL.Bytes → RSL.Env → Bool) (allocation234 : RSL.TX2_234.Args → RSL.Env → Nat → Bool)
  (ch : NMX_R4_Authentication.Choices) (alloc2 : NMV_ConcreteWindows.Allocation) (fx : AspisR1.NOC_Run5bCtx.Fixed)
  (w : AspisR1.NOC_Run5bCtx.World W Tx) (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
  (queries :
    @RSL.TASB.ExecB.QueriesF (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
      (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx)
  (run :
    @RSL.TASB.Runs (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) NNH_Libraries.L NNH_Libraries.V0 NNH_Libraries.VL
      (AspisR1.NNH_Run6Installed.implementation allocation217 allocation234 ch AspisR1.NNG_Candidate344.allocation
        alloc2)
      (@RSL.TASB.ctxB (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std)
        (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx w H)),
  have c : RSL.TAS.Sig.Ctx (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) :=
    @RSL.TASB.ctxB (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std)
      (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx w H;
  And
    (RSL.TAS.Sig.Bound (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c
      (RSL.TAS.Sig.model1 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c)
      (RSL.TAS.Sig.model2 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c))
    (And
      (@AspisR1.NNH8_Split.rest W Tx L0 copy c (RSL.TAS.Sig.model1 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c)
        (RSL.TAS.Sig.model2 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c))
      (Or
        (@RSL.EVB.HeadlineB.OutcomeRec (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
          (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_HeadlineB.headlineB W Tx L0 borrow copy std) c
          (RSL.TAS.Sig.model1 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c)
          (RSL.TAS.Sig.model2 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c))
        (@RSL.TASB.ExecB.ERec (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
          (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx H)))
```

### How to read it

The statement is one long "for every" followed by a conclusion, and its
strength lies in how much it ranges over. It holds for every state the Solana
runtime could be in, every pattern of memory allocations succeeding or failing,
every hash function and every attacker, where the attacker is an arbitrary
program that may query the hash function, choose the first transaction, see
what happened and query again before choosing the second. The only things held
fixed are the verifier's own code and its deployed configuration.

Two hypotheses say what kind of run is being considered. One sets the
attacker's budget, saying that it makes at most Q hash queries in total, with
repeated queries and queries made before a rejection all counted. Q is the
parameter of the bound and places no restriction on how the attacker behaves.
The other describes the two-transaction game: the two transactions ran one
after the other on the same chain history, both used the same checkpoint with
nothing else touching it in between, and both returned successfully. This is
also where the pool comes in, since everything in that history that is not the
verifier's doing is taken to be what the pool and the runtime did, and the
theorem proves nothing about the pool itself.

The theorem relies on four stated assumptions about code outside Aspis. They
are that the Solana account library lends out account data as documented, that
the standard library's slice copy behaves as documented, that the runtime
starts each program with a valid heap and consistent accounts, and that data
written by a successful transaction is what the next transaction loads. Each is
set out with its scope in [`TRUST-INVENTORY.md`](TRUST-INVENTORY.md).

The conclusion says three things. The first is the number: the model's failure
probability is at most total(Q), the bound given below. The second is that
every other part of the security statement holds, which covers the spend
claims, the protection of the checkpoint and the facts that tie the model to
the installed code. The third concerns the run in question, and says that
either the outcome required by the security statement holds or the attacker's
own run contains a hash collision. That collision event is already counted
inside total(Q), so it adds nothing to the bound.

The table at the end of this page says what each named symbol in the statement
stands for.

## The second theorem

Lean prints the statement of `deployed_charge` as follows.

```
@AspisR1.TAS_FinalB.deployed_charge : ∀ {W Tx : Type}
  (L0 : AspisR1.S2Trust.Library W (Nat → AspisR1.S2W_D189Entry.Record))
  (borrow : @AspisR1.S2Trust.S2TrustedSdkBorrow W (Nat → AspisR1.S2W_D189Entry.Record) L0)
  (copy :
    AspisR1.S2Trust.Heap (Nat → AspisR1.S2W_D189Entry.Record) →
      Nat → AspisR1.S2Trust.Payload → AspisR1.S2W_TrustedStd.Outcome (Nat → AspisR1.S2W_D189Entry.Record))
  (std : @AspisR1.S2W_TrustedStd.TrustedStd (Nat → AspisR1.S2W_D189Entry.Record) copy)
  (allocation217 : RSL.Bytes → RSL.Env → Bool) (allocation234 : RSL.TX2_234.Args → RSL.Env → Nat → Bool)
  (ch : NMX_R4_Authentication.Choices) (alloc2 : NMV_ConcreteWindows.Allocation) (fx : AspisR1.NOC_Run5bCtx.Fixed)
  (anchor : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State)
  (queries :
    @RSL.TASB.ExecB.QueriesF (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
      (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx)
  (wOf : (AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State) → AspisR1.NOC_Run5bCtx.World W Tx),
  And
    (∀ (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State),
      @LE.le.{0} Rat Rat.instLE
        (@Max.max.{0} Rat Rat.instSup (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
          (RSL.TASB.ind
            (And
              (@RSL.TASB.Runs (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) NNH_Libraries.L NNH_Libraries.V0
                NNH_Libraries.VL
                (AspisR1.NNH_Run6Installed.implementation allocation217 allocation234 ch
                  AspisR1.NNG_Candidate344.allocation alloc2)
                (@RSL.TASB.ctxB (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
                  (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx (wOf H) H))
              (Not
                (@RSL.EVB.HeadlineB.OutcomeRec (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
                  (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std)
                  (@AspisR1.NNH8_HeadlineB.headlineB W Tx L0 borrow copy std)
                  (@RSL.TASB.ctxB (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
                    (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx (wOf H)
                    H)
                  (RSL.TAS.Sig.model1 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
                    (@RSL.TASB.ctxB (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
                      (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx (wOf H)
                      H))
                  (RSL.TAS.Sig.model2 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
                    (@RSL.TASB.ctxB (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std)
                      (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std) (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx (wOf H)
                      H)))))))
        (RSL.TASB.ind
          (@AspisR1.BinRawByteCollisionTargets.event
            (AspisV8R19.MemoizedProgramLaw.View AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
              (AspisR1.GExq_AccountExperiment.Outcome Bool))
            (@FS2.Duplex.Params.iv AspisR1.SelectedTranscriptParams.Message AspisWideTower.WideExact
              AspisR1.SelectedTranscriptParams.L AspisR1.SelectedTranscriptParams.params)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (AspisR1.NNH_HostCtx.Fixed.Q0 fx)
                (AspisR1.NNH_HostCtx.Fixed.Q1 fx))
              (@OfNat.ofNat.{0} Nat (nat_lit 2965) (instOfNatNat (nat_lit 2965))))
            (@AspisV8R19.MemoizedProgramLaw.eval AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
              (AspisV8R19.MemoizedProgramLaw.View AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
                (AspisR1.GExq_AccountExperiment.Outcome Bool))
              H (AspisR1.NNH8_RecorderFixed.fixedProgram copy fx anchor)))))
    (And
      (@LE.le.{0} Rat Rat.instLE
        (@AspisV8R19.MemoizedProgramLaw.lazyMean AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
          (AspisV8R19.MemoizedProgramLaw.View AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
            (AspisR1.GExq_AccountExperiment.Outcome Bool))
          (@Pi.instFintype.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
            (fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))) =>
              AspisV8R19.DuplexFrames.Byte)
            (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
            (SimplexCategory.instFintypeToTypeOrderHomFinHAddNatLenOfNat
              (SimplexCategory.mk (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))))
            fun (a : Fin (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))) =>
            SimplexCategory.instFintypeToTypeOrderHomFinHAddNatLenOfNat
              (SimplexCategory.mk (@OfNat.ofNat.{0} Nat (nat_lit 255) (instOfNatNat (nat_lit 255)))))
          (fun (a b : AspisV8R19.DuplexFrames.Bytes) =>
            @instDecidableEqList.{0} AspisV8R19.DuplexFrames.Byte
              (instDecidableEqFin (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256)))) a b)
          (AspisR1.NNH8_RecorderFixed.fixedProgram copy fx anchor)
          (@FS.emptyTable AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State)
          fun
            (v :
              AspisV8R19.MemoizedProgramLaw.View AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
                (AspisV8R19.MemoizedProgramLaw.View AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
                  (AspisR1.GExq_AccountExperiment.Outcome Bool))) =>
          AspisV8R19.CausalFirstHitUnionBound.indicator
            (@AspisR1.BinRawByteCollisionTargets.event
              (AspisV8R19.MemoizedProgramLaw.View AspisV8R19.DuplexFrames.Bytes AspisV8R19.SourceDuplexStep.State
                (AspisR1.GExq_AccountExperiment.Outcome Bool))
              (@FS2.Duplex.Params.iv AspisR1.SelectedTranscriptParams.Message AspisWideTower.WideExact
                AspisR1.SelectedTranscriptParams.L AspisR1.SelectedTranscriptParams.params)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (AspisR1.NNH_HostCtx.Fixed.Q0 fx)
                  (AspisR1.NNH_HostCtx.Fixed.Q1 fx))
                (@OfNat.ofNat.{0} Nat (nat_lit 2965) (instOfNatNat (nat_lit 2965))))
              v))
        (AspisR1.F3T_Numeric.total
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (AspisR1.NNH_HostCtx.Fixed.Q0 fx)
            (AspisR1.NNH_HostCtx.Fixed.Q1 fx))))
      (∀ (H : AspisV8R19.DuplexFrames.Bytes → AspisV8R19.SourceDuplexStep.State),
        have c : RSL.TAS.Sig.Ctx (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) :=
          @RSL.TASB.ctxB (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) (@AspisR1.NNH8_Exec.recSig W Tx L0 copy std)
            (@AspisR1.NNH8_Exec.exec W Tx L0 copy std) fx (wOf H) H;
        @LE.le.{0} Rat Rat.instLE
          (AspisR1.F3T_RuntimeBound.failureModel
            (@AspisR1.NOC_Run5bHost.runtime W Tx L0 copy c
              (RSL.TAS.Sig.model1 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c)
              (RSL.TAS.Sig.model2 (@AspisR1.NOC_Run5bHost.S_host W Tx L0 copy std) c)))
          (AspisR1.F3T_Numeric.total
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (AspisR1.NNH_HostCtx.Fixed.Q0 fx)
              (AspisR1.NNH_HostCtx.Fixed.Q1 fx)))))
```

### How to read it

The second theorem has the same ingredients, with the hash function no longer
fixed. The state of the world is allowed to depend on the hash function in any
way, and the description of the run moves out of the hypotheses and into the
event whose probability is being measured.

Its conclusion again says three things. For every hash function, a run in which
both transactions are accepted but the security statement fails lies in the
collision event. The probability of that collision event, taken over a random
hash function, is at most total(Q). And for every hash function the model's
failure probability is at most total(Q). Together these give the averaged
claim, since a false spend always lies inside the collision event and the
collision event is rare. The theorem states the two facts separately and does
not itself write the average as a single quantity, which the
[status document](SOUNDNESS-STATUS.md) records. The average is taken over all
hash functions with nothing conditioned on, so every case counts with its full
weight.

## The bound

The function total(Q) is defined in Lean as

```
total(Q) = (Q+34)·B + 6·(Q+1161)²/2^256 + 6·(Q+2965)²/2^256 + 2^-126 + 2^-454
B        = 15/2^109   (about 2^-105.09)
```

where Q is the number of hash queries the attacker issues across both phases,
counting duplicates and every query before a rejection. The first term charges
each fresh transcript start, the attacker's Q queries together with the 34
starts the submitted transcript itself reads before terminal authentication,
with probability at most B of succeeding. The
two squared terms are collision terms, one over the verifier's first reads and
one over the reads recorded in the attacker's own run, and the last two are an
allowance for the extractor aborting and for the query scan running out.

For any feasible Q the first term dominates, so total(Q) is about
(Q+34)·2^-105.09. Lean also proves that total(Q) is at
most (Q+1)·2^-100 exactly when Q is at most about 2^152.37, and that with no
attacker queries at all total(0) falls short of 2^-100 by about 2^-108. The
figure takes no credit for proof-of-work or grinding. It bounds a single run of
the spend experiment, in which repeated attempts within the run are fully
counted; a bound across separately submitted attempts is one of the open items.
The derivation of every term is in section 3 of
[`SOUNDNESS-STATUS.md`](SOUNDNESS-STATUS.md).

## The symbols in the statements

| Binder | Meaning |
| --- | --- |
| `W`, `Tx` | Types of runtime worlds and transactions, arbitrary |
| `L0` | Model of the Solana account library the verifier borrows account data from |
| `borrow` | Assumption that `solana-account-info` 2.3.0 lends account data and guards it as documented |
| `copy` | The heap slice-copy operation |
| `std` | Assumption that the pinned standard library's `copy_from_slice` behaves as documented |
| `allocation217` | Allocation success while decoding the lane from the pool's release data |
| `allocation234` | Allocation success while authenticating the release registry |
| `ch` | Three allocation decisions while authenticating the second transaction's accounts |
| `alloc2` | Allocation success for the working windows of the second stage |
| `fx` | Everything that does not depend on the hash function: the adaptive attacker `fx.a`, the query budgets `Q0` and `Q1` for its two phases, the derivation of program addresses, the clock reading, the allocator's reservation bit and fixed program data |
| `w` | The state of the run: the two runtime worlds, the saved checkpoint bytes, the heaps after each stage, the two transactions and the list of runtime actions (first theorem) |
| `wOf` | A world for each oracle, arbitrary (second theorem) |
| `H` | The random oracle modelling SHA-256 |
| `anchor` | A fixed hash function used only to build the recorder program (second theorem) |
| `queries` | The query budget: at most `Q0 + Q1` hash queries, whatever the oracle |
| `run` | The two-transaction game, with the runtime assumptions and the pool's recorded actions (first theorem) |

The numbers in three of the allocation binders are rows of the
[function ledger](LEDGER-599.md).

## How the proofs were checked

`#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`
for both theorems and for every term installed in them. There is no `sorry`, no
project-specific axiom and no `native_decide`. As an independent check, a
separate program walked the proof terms directly, following every edge from
each theorem through roughly 146,000 constants, and reached exactly the same
three axioms. A scan of the whole closure found no dangling reference, no
declaration defined twice and no import that differs from its recorded source.

The audit also confirms that the printed statements contain no hypothesis about
the value of a particular digest, no assumption that the hash is injective, no
premise asserting that the submitted transactions realise the attacker's
choice (they are defined as the attacker's output), and no new trust
assumption, and that the attacker is universally quantified and never a
constant.

Lean checks these proofs about the model the statements name. Whether the
translated Lean definitions are faithful to the deployed program, whether the
deployed binary computes what the source says, and whether the trusted
assumptions hold of the real runtime are separate questions, and they are the
open items listed in [`OPEN-GATES.md`](OPEN-GATES.md).

## A correction to the host model

Before 9 November 2026 the model of the host environment left one operation,
the zero-filled buffer allocation at the start of the first stage, as a
placeholder that never returns. Lean proved the consequence directly: under
that model the first transaction could never be accepted, so a theorem stated
there would have said nothing about real runs. The corrected model installs the
allocation as the frozen source writes it, returning a zeroed buffer when the
reservation succeeds and an allocation error otherwise, under the existing
assumption about the allocator, and Lean proves that only that operation and
one SDK slot changed. No contract text and no trust assumption changed. Both
theorems on this page are stated at the corrected host.

## Where this comes from

The statements above are copied character for character from the audit record
[`TAS_G0_AUDIT.json`](TAS_G0_AUDIT.json) (field `kernel_statements_verbatim`),
which holds Lean's output with `set_option pp.all true` and `pp.proofs false`.
The Lean source that proves them is [`TAS_FinalB.lean`](TAS_FinalB.lean). Both
are copied unchanged from commit `07123926e88` of the
[`research`](https://github.com/DJBarker87/aspisZK/tree/research) branch, and
the theorems are about the frozen source at revision `4bb3b3f`. Their full
names are `AspisR1.TAS_FinalB.deployed_splitB` and
`AspisR1.TAS_FinalB.deployed_charge`.
