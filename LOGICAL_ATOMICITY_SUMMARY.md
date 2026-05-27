# Logical Atomicity for Pulse/F* — Project Summary

## Status: 49 commits on `feature/logical-atomicity`

### What Has Been Built (All Verified)

#### Core Library (zero admits)
- **`Pulse.Lib.LogicalAtomicity.fsti/fst`** — AU encoding using FlippableInv + trades
  - `au_token`, `au_available`, `au_opened` — reified AU protocol
  - `au_intro`, `au_open`, `au_abort`, `au_commit` — all verified
  - `lat`, `lat_void` — LAT types that structurally prevent spec hacking (Φ universally quantified)
  - `lat_elim`, `lat_open` — composition rules
  - Commit trade: `trade #is (later_credit 1 ** β(x,y)) (Φ(x,y))`
  - `is:inames` parameter on `au_commit` for mask-parameterized trades

- **`Pulse.Lib.AtomicPrimitives.fsti/fst`** — Trusted atomic kernel (opaque .fsti, model .fst with `as_atomic`)
  - `atomic_read`, `atomic_write`, `atomic_alloc`, `atomic_cas`, `atomic_cas_box`, `atomic_faa`
  - `ll` (load-linked), `sc` (store-conditional) — for nested LP example
  - `cond b p q` helper

- **`Pulse.Lib.PersistentPtsTo.fst`** — `persistent_pts_to r v = ∃q. B.pts_to r #q v`
  - `make_persistent`, `dup_persistent`, `read_persistent` (erased-compatible)

- **`Pulse.Lib.Prophecy.fst`** — Ghost-ref infrastructure (zero admits)
  - `prophecy_var`, `prophecy_token`, `prophecy_handle` — split ghost ref pattern
  - `prophecy_alloc`, `prophecy_set`, `prophecy_agree`, `resolve`

#### PulseCore Semantics Extension (zero admits)
- **`PulseCore.Semantics.fst`** — Added `Angel` constructor to computation monad `m`
  - `| Angel: decode:(nat→c) → k:(c → Dv (m a pre post)) → m a pre post`
  - `step`: Angel reads from angel oracle via `NST.angel()`
  - `mbind`, `frame`, `apply_hom`: all distribute through Angel correctly

- **`PulseCore.NondeterministicHoareStateMonad.fst`** — Extended with angel tape
  - Demonic tape: `nat → bool` (scheduler, universally quantified)
  - Angel tape: `nat → nat` (prophecy oracle, existentially quantified in adequacy)
  - `angel()`: reads from angel tape, increments shared counter

- **`PulseCore.PartialNondeterministicHoareStateMonad.fst`** — Threaded angel tape
- **`PulseCore.InstantiatedSemantics.fst`** — Verified unchanged

#### Examples (all verified, zero admits)
| Example | File | Key Features |
|---------|------|-------------|
| FAA via CAS | `PulseTutorial.FAAviaCAS.fst` | Canonical LA demo, `faa_is_lat`, `composed_faa` (non-trivial Φ) |
| Atomic Counter | `PulseTutorial.AtomicCounter.fst` | CAS-loop increment, `incr_is_lat` |
| Counter+Backup | `PulseTutorial.CounterWithBackup.fst` | FAA-based counter |
| Treiber Stack | `PulseTutorial.TreiberStack2.fst` | Push+Pop with persistent `is_list`, `push_is_lat`, `pop_is_lat` |
| Conditional Incr | `PulseTutorial.ConditionalIncrement.fst` | Persistent flag, `cinc_is_lat` |
| RDCSS | `PulseTutorial.RDCSS.fst` | AU spec with CAS-retry, `rdcss_is_lat` |
| Atomic Snapshot | `PulseTutorial.AtomicSnapshot.fst` | Two-phase write, `write_is_lat` |
| Nested LP | `PulseTutorial.NestedLP.fst` | FAA via CAS via LL/SC — true two-level nesting |
| Nested Invariants | `PulseTutorial.NestedInvariants.fst` | Proof-of-concept: two invariants open simultaneously |
| Elimination Stack | `PulseTutorial.EliminationStack.fst` | Push only |

---

### Key Technical Decisions

#### AU Encoding
- FlippableInv pattern: ghost bool ref + invariant
- `au_inv_p`: when flag=true, holds `∃x. α(x) ** ∀*y. trade #is (later_credit 1 ** β(x,y)) (Φ(x,y))`
- `au_opened(x)` indexed by phantom `x` — prevents open-at-x₁/commit-at-x₂
- `au_commit` uses `elim_trade #is` — fires stored trade, drops remnants

#### Nested Invariant Opening
- Pulse DOES support nested `with_invariants_a` (proven in `NestedInvariants.fst`)
- Key: outer call's `is` must anticipate inner openings: `with_invariants_a _ (add_inv emp i2) i1 ...`
- Foundation for bigatomic-style proofs (CachedWaitFree)

#### Modular Nested LP Composition
- `faa_modular` calls `cas_commit_only` as a BLACK BOX
- Inner CAS's Φ commits outer FAA's AU via trade chain
- `β_inner` carries `pure(n == expected)` enabling rewrite for outer commit
- No disjoint namespace needed — `au_commit` uses `opens emp_inames`

#### read_persistent erased fix
- `read_persistent` takes `#v : erased a` (not `#v : a`) — matches `B.op_Bang`
- Fixes ghost-scope issue where `stt` ops were blocked after ghost fns with erased returns

---

### Prophecy Variables — Current Status and Path Forward

#### What We Have
1. **Angel constructor** in `PulseCore.Semantics.m` — zero admits, fully integrated
2. **Angel tape** in NST/PNST monads — `nat → nat`, read by `NST.angel()`
3. **Ghost ref infrastructure** — `prophecy_alloc/set/agree/resolve` — zero admits
4. **`run_alt`** takes both demonic and angel tapes

#### What's Missing: The Coupling
The equality `predicted_v == actual_result` requires coupling between the angel tape and physical action results. In Iris, this coupling lives in the **state interpretation**:

- Iris's `state_interp σ κs` receives the full observation trace `κs` (universally quantified in adequacy)
- `proph_map_interp κs ps` seeds a ghost map from `κs`
- `proph p pvs` is a ghost map fragment — user gets `pvs = proph_list_resolves κs p`
- At `Resolve`, ghost map update proves `pvs = (result, tag) :: pvs'`
- The equality is a CONSEQUENCE of ghost map agreement, not an axiom

#### How to Implement in Pulse

The approach requires extending the state interpretation to include the observation trace:

1. **Extend the instantiated state** (`Sep.full_mem` or a product state) with an observation list
2. **`state.invariant`** (or a new field) incorporates `proph_map_interp` tracking the observation list
3. **`prophecy_alloc`** uses `Angel` to read from angel tape AND allocates a ghost map entry seeded from the observation list in the invariant
4. **`resolve`** (as an action) runs the physical step AND consumes the head of the observation list from the invariant, proving agreement via ghost map update
5. **Adequacy**: `run_alt` universally quantifies over the angel tape. The angel tape determines the observation list. For the actual execution, everything is consistent.

Key files to modify:
- `PulseCore.InstantiatedSemantics.fst` — extend `state0` to include observation state
- `PulseCore.MemoryAlt.fsti/fst` or a new prophecy memory module — define `proph_map_interp`
- `PulseCore.Action.fst` — add `resolve_action` that consumes observation head
- `Pulse.Lib.Prophecy.fst` — wire to the new state interpretation

#### Key Insight from Iris (POPL 2020)

The "future knowledge" is an ILLUSION created by universal quantification:
- The user's proof works for ALL possible observation lists `κs`
- The user case-splits on the head of `pvs` (predicted next value)
- Both branches are verified
- The actual execution produces a specific `κs_actual`
- Adequacy instantiates the universal with `κs_actual` — consistency follows

No circularity, no seeding, no prediction. Just universal quantification over traces.

#### Iris Source References
- `iris/base_logic/lib/proph_map.v` — ghost map RA, `proph_map_interp`, `proph_map_new_proph`, `proph_map_resolve_proph`
- `iris_heap_lang/primitive_laws.v` — `wp_new_proph`, `wp_resolve`
- `iris_heap_lang/lang.v` — `NewProphS`, `ResolveS` operational steps
- `iris/program_logic/adequacy.v` — `wp_adequacy_gen` with `κs` parameter

---

### Known Gaps vs Iris

| Gap | Description | Severity |
|-----|-------------|----------|
| No greatest fixpoint | `au_intro` requires concrete α(x₀) + trade, not persistent coinductive accessor | Fundamental but hasn't blocked any example |
| Single `is` vs Eo/Ei | `trade #is` is positive footprint, not Iris's cofinite mask algebra | Works for all current examples including nested |
| `lat_open` restricted | Commit-only postprocessing, not full aacc_aupd_commit | Addressable |
| Prophecy coupling | Missing state-interpretation extension for observation trace | The main remaining work |
| No telescopes | Use product types manually | Minor |

---

### Environment

- F* 2026.05.17 at `/home/t-zakkent/.local/bin/fstar`
- Z3 4.13.3 at `/home/t-zakkent/.local/bin/z3-4.13.3`
- Pulse ulib at `/home/t-zakkent/fstar-lib/ulib` and `/home/t-zakkent/fstar-lib/ulib.checked`
- Git branch: `feature/logical-atomicity`
- Working directory: `/home/t-zakkent/research/FStar`

Full verification command:
```
cd /home/t-zakkent/research/FStar && fstar \
  --include /home/t-zakkent/fstar-lib/ulib \
  --include /home/t-zakkent/fstar-lib/ulib.checked \
  --include pulse/lib/core \
  --include pulse/lib/pulse/lib \
  --include pulse/lib/pulse/lib/pledge \
  --include pulse/lib/pulse/lib/class \
  --include pulse/lib/common \
  --include pulse/lib/pulse/c \
  --include pulse/share/pulse/examples/by-example \
  <file.fst>
```

### Bigatomic/CachedWaitFree Reference
- Repo: `github.com/cmuparlay/bigatomic-mechanization`
- Paper: `arxiv.org/pdf/2501.07503`
- Three namespaces: `readN`, `casN`, `cached_wfN` — all sub-namespaces of `N`
- AU at `⊤ ∖ ↑N, ∅` — CAS opens `cached_wfN`, calls `read'` (LAT at `↑readN`)
- Both invariants open simultaneously at LP
- `execute_lp`: opens `casN` + commits AU in one step
- `linearize_cas`: helping — linearizes all failing CAS operations
