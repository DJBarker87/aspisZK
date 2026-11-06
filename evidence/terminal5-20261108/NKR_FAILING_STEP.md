# NKR failed steps

K001 NKR_schedule_cut: CBMC90second timeout, exit1,100.805869s wall,2105352KiB peak RSS,swap0. No credit. Whole3call/all-carrier shape retired; no unchanged rerun or cap/time increase. Replacement: first-child argument/tuple window, arbitrary single-preweighted state window, source-order composition; different smaller formulas. K002 control never launched.

K003: own validation source-hash mismatch after splitting schedule; no Kani launched. ReplacementK011 includes committed NKR_UPDATE.patch and same-or-stricter frozen/source/lock checks; passed.

L001: inherited path omitted NKH_COMBINED_IMPORT. L002 adds NKN retained closure search paths and passes; no changed upstream object.
L003: own reserved identifier prefix. L005/L008: missing list.take/zip proof then recursive simplifier goal; replaced by explicit structural induction. L007: unretargeted carry import duplicates FIq owner; changed only new NKR_DigestCarry imports/proof, existing owners untouched. Failed logs including Lean's error-generated sorryAx are retained and earn no credit.

K005 isolated first-child/fullcarrier window timedout96.959745s,1641808KiB,swap0;retired. ReplacementsK012/013public,K014/015data,K016/017tuple,K007/008weightPASS/FAIL. K018prefix andK024batch/K026pattern/K028tail failed only input-generation loop0 unwinding;preserved,bound-only repairprepared,same originalharnessnames/properties,caps/timeouts unchanged. K020middle andK022wrapper timedout97.082087/96.822726s,1467812/2024664KiB,swap0;retired,replacementsmustsplit. Theircontrols notlaunched. K030/031terminal suffix andK032/033errorprefixPASS/FAIL.
