import BinCanonicalCutWords
import TableLogRepresentative
import CanonicalCutEnrichedTranscript

/-! Concrete table-only recovered-word functions for the three commitment
rows. Unlike the earlier represented-log interface, these functions have no
trace or future-oracle argument. The specification-level table representative
is total; efficient extraction remains a separate obligation. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawByteTableWordsBin

open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.AdaptiveFirstReadLaw
open BinRawByteCutRecovery BinRawByteCutStability CanonicalCutEnrichedTranscript

/-- Recover solely from the table supplied at a commitment's first read. -/
def recoverFromTable (T : Table Bytes State) (tag : BinMerkle32Path.Byte) (width : Nat)
    (slots : List (Fin 2)) (root : State) : Option BinMerkleLeafRecovery.LeafData :=
  recoverAt tag width (TableLogRepresentative.logOf T) slots root

def c1Map (T : Table Bytes State) (root : State) : Fin 262144 → Option Bytes :=
  fun q => (recoverFromTable T 0x71 480 (BinMultiproof.slots 18 q.val) root).map Prod.fst

def c2Map (T : Table Bytes State) (root : State) : Fin 262144 → Option Bytes :=
  fun q => (recoverFromTable T 0xf1 128 (BinMultiproof.slots 18 q.val) root).map Prod.fst

def foldedMap (T : Table Bytes State) (root : State) : Fin 65536 → Option Bytes :=
  fun q => (recoverFromTable T 0x72 128 (BinMultiproof.slots 18 q.val) root).map Prod.fst

def words (T0 T2 T30 : Table Bytes State) (root0 root2 root30 : State) : Words :=
  wordsFromMaps (c1Map T0 root0) (c2Map T2 root2) (foldedMap T30 root30)


#print axioms recoverFromTable
#print axioms words
end AspisR1.RawByteTableWordsBin
end
