# `PulseTutorial.Seqlock` audit

This audit records the proof-engineering and extraction assumptions for the
seqlock LAT port committed in `PulseTutorial.Seqlock.fst` and the supporting
library additions. It documents accepted proof boundaries; it does **not**
change any proof, relax any verification gate, or introduce any axiom.

The port comprises six commits on `feature/pulse-lat-examples`:
- `83203cea1c` — Phase 0: `Pulse.Lib.SeqlockHistory` library.
- `4722b2f41f` — Phase 1: `seqlock_inv`, `is_seqlock`, `new_big_atomic`.
- `a39960f133` — Phase 2: `snapshot_copy` with per-element evidence.
- `56dabbee5b` — Phase 3: `write` LAT with the linearization point at the
  successful lock-acquiring CAS, and `Pulse.Lib.Primitives.cas_nat`.
- `d67301f96e` — Phase 4: `read` LAT with the LP at the second version-read
  on the equal-and-even branch.
- (this commit) — Phase 5: polish, audit doc, regression-target cleanup.

## `as_atomic` taxonomy

The seqlock port wraps six machine-level operations with
`Pulse.Lib.Core.as_atomic`. Each entry below names the wrapper, the operation
it models, the actual hardware atomicity requirement, and the extraction
assumption being made. The `Class` column distinguishes single-operation
loads/stores (`MACHINE-ATOMIC`) — where atomicity follows directly from a
naturally aligned aligned hardware load/store at the right type — from CAS
(`RUNTIME-ATOMIC`) — where atomicity requires a hardware compare-exchange
instruction or a lock-wrapped runtime.

| ID | Wrapper | Site | Machine op modeled | Hardware atomicity | Extraction assumption | Class |
|---|---|---|---|---|---|---|
| A1 | `snapshot_read_slot_atomic` | Phase 2 reader copy loop | One `val_t` load from `data.(i)` while the invariant is open | Single aligned load if `val_t` extracts to a machine word | Backend must not compile this as a tearable multi-word read; with `val_t = int`, production extraction should refine `val_t` to a machine-word type | `MACHINE-ATOMIC` (subject to `val_t` refinement) |
| A2 | `version_read_atomic` | Phase 3/4 readers and writer polling | `!version` for both reader version polls and writer lock-state polling | Single aligned load after version-word refinement | Same load semantics required by `cas_nat`'s success/failure agreement; refine `version` to `U32.t`/`U64.t` for trivial extraction | `MACHINE-ATOMIC` (subject to `ref nat` refinement — see next section) |
| A3 | `version_store_bool_atomic` | Phase 3 writer final unlock store | `version := start_ver + 2` (release the lock by returning the version word to even) | Single aligned store after version-word refinement | This store is the second of two atomic steps in the writer's epilogue (CAS = LP step 1; this store = lock release); a hardware aligned store suffices | `MACHINE-ATOMIC` (subject to refinement) |
| A4 | `data_write_slot_atomic` | Phase 3 writer copy loop | One `val_t` store into `data.(i)` while the invariant is in its odd branch | Single aligned store if `val_t` extracts to a machine word | Same refinement caveat as A1; readers' A1 loads concurrent with these A4 stores must not tear | `MACHINE-ATOMIC` (subject to `val_t` refinement) |
| A5 | `Pulse.Lib.Primitives.cas_nat` | Phase 3 writer lock acquisition; the LP step | Atomic compare-exchange on `version` with `start_ver` expected, `start_ver + 1` new | Genuine hardware CAS or lock-wrapped runtime — NOT a load-store sequence | The backend for `Pulse.Lib.Primitives.cas_nat` must implement a linearizable atomic CAS on the extracted version representation and preserve the success/failure ownership contract exposed in its `.fsti` | `RUNTIME-ATOMIC` |

### Phase 3 attempt-1 anti-pattern, for the record

During the Phase 3 implementation effort, attempt 1 inlined a local
`version_cas_atomic = as_atomic (let old = !version; if old = expected { version := newv })`
inside `PulseTutorial.Seqlock.fst`. The Phase 3 reviewer flagged this as a
soundness hole — two writers can both read `version = 0`, both fall into the
true branch, and both reach the store, producing two CAS-success returns
under a single physical-CAS premise. **This is not equivalent to a CAS.**
The fix (attempt 2, shipped in `56dabbee5b`) was to add `cas_nat` as a real
primitive in `Pulse.Lib.Primitives` whose runtime must back it with a true
atomic CAS instruction. The lesson: `as_atomic` is acceptable for a wrapper
around a *single* hardware-atomic op (A1–A4) but is unsound when wrapping a
load-then-store sequence intended to be a CAS.

## `ref nat` extractability story

`Pulse.Lib.Primitives.cas_nat` and the version-cell `as_atomic` wrappers
operate on `ref nat`, where `nat` is F\*'s unbounded arithmetic type. There is
no hardware CAS for unbounded nats; this is a proof-level convenience matching
the Iris seqlock presentation.

**Recommended path: option A — refine the version reference to a bounded
machine word.**

1. Replace the physical version cell in `big_atomic` with `ref U64.t` (or
   `ref U32.t` where appropriate).
2. Keep the monotone ghost version `mono_nat_auth` as a mathematical `nat`,
   related to the physical word by an invariant-side embedding predicate.
3. Either prove every write increments within range for the verified
   execution bound, or specify a wraparound discipline and update the read
   protocol accordingly.
4. Replace `cas_nat`, `version_read_atomic`, and `version_store_bool_atomic`
   with word-sized atomic primitives (existing `U32` `cas`, future `U64`).

**Option B — arbitrary-precision atomic backend for `ref nat`** — would
require linearizable load/store/CAS over bignum objects in the runtime. That
backend is heavier than the seqlock implementation model warrants and is not
recommended outside an interpreter/testing backend.

## TCB extension inventory

The port made the following changes outside `PulseTutorial.Seqlock.fst`.

| File | Port change | TCB assessment |
|---|---|---|
| `pulse/lib/pulse/lib/Pulse.Lib.SeqlockHistory.fsti` | Added the abstract history ghost API: `history_auth`, persistent `history_frag`, allocation, sharing/gathering, `history_extend`, fragment allocation, and agreement lemmas | Acceptable library surface. Interface is semantic and closed: clients only obtain fragments through verified operations and agreement exposes only list-index facts. No axioms. |
| `pulse/lib/pulse/lib/Pulse.Lib.SeqlockHistory.fst` | Implemented the API using `Pulse.Lib.MonotonicGhostRef` over a prefix preorder on histories | Acceptable as verified ghost code. Uses available Pulse `MonotonicGhostRef` machinery; `history_extend`, `history_frag_alloc`, `history_auth_frag_agree`, `history_auth_auth_agree` together recover the Iris auth-update / fragment-allocation / fragment-authority-agreement / auth-auth-agreement obligations needed by both the write and read proofs. |
| `pulse/lib/pulse/lib/Pulse.Lib.Primitives.fsti` | Added `cas_nat` as a primitive-boundary atomic CAS on `ref nat` | Acceptable with the extractability follow-up above. Mirrors the existing `U32` `cas` spec shape; exposes a closed success/failure ownership contract. |
| `pulse/lib/pulse/lib/Pulse.Lib.Primitives.fst` | Added `cas_nat_impl` and lifted it with `Pulse.Lib.Core.as_atomic` | Acceptable as the verification model for the primitive boundary. Follows the existing `U32 cas` idiom verbatim. Real extraction must replace this boundary with a hardware CAS or lock-backed runtime, per the recommendation above. |
| `pulse/share/pulse/examples/by-example/PulseTutorial.SeqlockHistoryTest.fst` | Added a regression test for the history API | Not a TCB extension; checked example exercising the public ghost interface. |
| `pulse/share/pulse/examples/by-example/PulseTutorial.Seqlock.AUDIT.md` | This document | Not code; not a TCB extension. |

## Deviation index

Aggregated declared deviations across all phases of the port. The shipped
proof's LP location (write at CAS, read at second version-read on the
equal-and-even branch) reflects deliberate Pulse-side choices justified
phase-by-phase below.

| Phase | Deviation | Reason class | Justification | Audit verdict |
|---|---|---|---|---|
| 0 | History ghost backend uses `Pulse.Lib.MonotonicGhostRef` over a prefix preorder, vs Iris's `authUR (gmapUR nat (agreeR (listO valO)))` | `DATA-ENCODING` | This Pulse branch exposes no `authUR` / singleton-fragment gmap API; the available mechanism for persistent monotone facts is `MGR.snapshot`/`recall_snapshot`. The seqlock-facing API (`history_extend`, `history_frag_alloc`, `history_auth_frag_agree`, `history_auth_auth_agree`) recovers the Iris obligations used by the seqlock proof | `ACCEPTED-AS-IS` |
| 2 | Single-slot atomic array load via `as_atomic` | `PULSE-PRIMITIVE-MISSING` | Pulse lacks `stt_atomic` for `Pulse.Lib.Array.PtsTo.op_Array_Access`; A1 wraps a single source-array load | `ACCEPTED-WITH-FOLLOWUP atomic-array-load-primitive` |
| 2 | `big_snapshot_evidence` includes `Forall (Nat.le ver_lb) vers` lower-bound fact and (incidentally) `StronglySorted Nat.le vers` | `LOGIC` | The lower-bound fact is load-bearing for the Phase 4 consistency proof: it lets the reader argue every per-element observed version dominates the initial version. The sortedness is incidentally true but non-load-bearing — readers do not need ordering between intermediate per-slot versions, only the lower bound and (via history_frag) the value agreement | `ACCEPTED-AS-IS` |
| 2 | Erased version witnesses (`FStar.Ghost.erased`) for invariant existentials returned alongside informative data | `DATA-ENCODING` | Invariant existential versions cannot be returned as informative data from `with_invariants`; `hide`/`reveal` keeps them ghost-only | `ACCEPTED-AS-IS` |
| 2 | `seqlock_inv_body` and pack helpers introduced as named slprops | `VERIFIED-EQUIVALENT-REWRITE` | Helpers preserve the same existentials, parity branches, fractions, monotone authority, history authority, and array ownership; they enable explicit `fold`/`unfold` choreography that Pulse SMT cannot infer | `ACCEPTED-AS-IS` |
| 3 | Write LP at the lock-acquiring CAS, vs Iris's LP at the final-store unlock | `VERIFIED-EQUIVALENT-REWRITE` | LP-anywhere-in-locked-region principle: between CAS-success and final-store, no other writer can interleave (lock held) and no reader can complete a successful read (readers spin on odd version). Therefore the abstract-state change is unobservable to clients regardless of where in `[CAS_success, final_store_inclusive]` the AU is committed. CAS is the Pulse-simplest choice: AU work fuses into one atomic step, copy and unlock are AU-free | `ACCEPTED-AS-IS` |
| 3 | History-length formula `1 + (ver + ver%2)/2` (parity-aware), vs Iris's uniform `1 + ver/2` | `VERIFIED-EQUIVALENT-REWRITE` | Follows directly from the LP-at-CAS choice: the new history entry is installed when version is odd (`ver+1`), so the odd branch's history length is one greater than Iris's. The formula agrees with Iris's on even versions | `ACCEPTED-AS-IS` |
| 3 | AU bracketing via `Pulse.Lib.LogicalAtomicity.au_atomic_step` with `Some y → r_post y ** beta x y` / `None → r_pre ** alpha x` body contract, vs Iris's inline `iMod "AU"` | `LAT-ENCODING` | `au_atomic_step` is Pulse's LAT primitive for atomic LP steps with possible retry; retry preservation is represented through the `None` (au_abort) branch rather than by keeping the AU unopened on failed attempts | `ACCEPTED-AS-IS` |
| 3 | `read_is_lat` / `write_is_lat` exposed via `Pulse.Lib.LogicalAtomicity.lat` type alias over an explicit `au_token`, vs Iris's `<<< ... >>> ... <<< ... >>>` bracket notation | `LAT-ENCODING` | Pulse's public logically-atomic surface is the `lat` alias plus a client-side `phi`; bracket notation is an Iris proof-mode-only sugar | `ACCEPTED-AS-IS` |
| 3 | `cas_nat` primitive added to `Pulse.Lib.Primitives` | `PULSE-PRIMITIVE-MISSING` | Pulse exposed `U32` CAS and box-pointer CAS but no `stt_atomic` CAS for `ref nat`. The added primitive mirrors `U32 cas` verbatim and is justified separately in the TCB inventory above | `ACCEPTED-WITH-FOLLOWUP ref-nat-extractability` |
| 4 | First-read evidence packaged in slprops `read_start_evidence` / `read_start_frag` rather than returned as informative data | `DATA-ENCODING` | Same constraint as Phase 2's erased witnesses: invariant existentials cannot leave `with_invariants` as informative data | `ACCEPTED-AS-IS` |
| 4 | Retry-path destination copy is `free`d before recursion | `DATA-ENCODING` | Pulse's linear `Pulse.Lib.Array.PtsTo.pts_to` ownership for the destination array must be consumed on the retry path; Iris relies on HeapLang allocation/GC. Note `Pulse.Lib.Array.PtsTo.free` is marked deprecated/unsound (model-implementation only); production code should switch to a non-leaking ownership transfer (e.g. caller-provided buffer) — flagged as follow-up | `ACCEPTED-WITH-FOLLOWUP array-free-deprecated` |
| 4 | `read_frame` packages `is_seqlock v gh n ** pure (n > 0)` as a single named slprop | `VERIFIED-EQUIVALENT-REWRITE` | Definitional unfolding to the inline Iris precondition; no resources differ | `ACCEPTED-AS-IS` |

## Outstanding work

The port verifies and proves logical atomicity for `read` and `write` against
the Iris-style spec. The following items are NOT addressed and would be
needed before claiming production-ready extraction:

1. **Version-word refinement.** `ref nat` → `ref U64.t` per the recommendation
   above; includes adapting `cas_nat`, `version_read_atomic`,
   `version_store_bool_atomic`, and the embedding invariant linking physical
   `U64` to ghost monotone `nat`.
2. **`val_t` refinement.** Replace `val_t = int` with a machine-word type or a
   bounded refinement so A1/A4 are bona fide single-machine-op accesses.
3. **`Pulse.Lib.Array.PtsTo.free` deprecation.** The Phase 4 retry path uses
   the deprecated `free`. Switch to caller-owned destination buffers (no
   allocation in `read`) or to a non-deprecated allocator.
4. **Atomic-array slot primitives.** Promote A1/A4 from `as_atomic`-wrapped
   helpers to dedicated `Pulse.Lib.AtomicPrimitives` operations once those
   primitives exist for arrays.
5. **`seqlockWf.v` port.** The wait-free variant (writer never blocks on
   readers) builds on this seqlock and adds a snapshot-protocol layer. Not
   started.
6. **`CachedWaitFree.v` port.** Strong (no-prophecy) variant building on
   `seqlockWf`. Not started.
7. **Performance characterisation.** Per-element atomic ops dominate cost;
   bulk transfer optimisations (e.g. `memcpy` under suitable atomicity model)
   are out of scope for the LAT proof but relevant for any deployment claim.

## Workflow notes for downstream phases

The seqlock-port workflow's phase reviewers are instantiated fresh and see
only current source. A reviewer for any successor phase that touches this
proof should treat the rows in the **Deviation index** as adjudicated:
re-litigation here is out of scope. If a successor phase needs to relax or
revise a prior-phase deviation, that must be an explicit phase deliverable
with its own contract change, not a side effect of polish or audit work.
