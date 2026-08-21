# Logical Atomicity for Pulse/F* — Project Summary

## Status: 49 commits on `feature/logical-atomicity`

### What Has Been Built (All Verified)

#### Core Library (verified; trusted primitive admits confined to existing atomic boundary)
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
  - current `new_proph_semantic`/Resolve scaffold for HeapLang-style NewProph/Resolve: `new_proph_semantic` consumes the active prophecy-id cursor but still initializes the public token stream locally instead of projecting it from a runner-owned singleton active component; `resolve_proph_token_semantic`/`resolve_proph_semantic` lower an observable atomic action through `ObservedResultAct` so the physical action and observation-tape read are coupled in one semantic step, but the tail/equality still depends on the remaining `resolve_proph_current_decode_witness`; the atomic-shaped `resolve_proph_token`/`resolve_proph` boundary for open-invariant clients factors through a local non-exported observed-result `stt_atomic` compatibility rule in `AtomicPrimitives` (still implemented by the trusted primitive-kernel coercion until PulseCore has a native action form, or auditors explicitly accept retaining this scoped seam temporarily)
  - verified first-class shared-authority resource slice: `prophecy_authority_state` owns one authoritative `proph_state_view_encoded`, `prophecy_authority_runtime_state` ties it to `NST.prophecy_index`, `NST.observation_index`, and the observation tape, `prophecy_shared_state_interp` names the exact `proph_map_interp`-style state-interpretation resource that adequacy must own, `prophecy_token_fragment` owns only an individual token slot, and `prophecy_authority_alloc` / `prophecy_authority_resolve_observed` update the shared authority plus token fragment with the checked Trace authority lemmas when supplied the allocation/observation facts; the public token now hides this runtime authority, and the counter-aware `prophecy_shared_state_interp_alloc` / `prophecy_shared_state_interp_resolve_current` wrappers open/update/close the named shared interpretation at `NST.bump_prophecy` and `NST.bump_observation`. Round 5 added `nst_obs_ctr`/`pnst_obs_ctr` and `prophecy_shared_state_interp_*_obs_ctr_repr` wrappers whose pre/post can mention the active observation tape and input/output `NST.ctr`. Round 8 additionally packages the authority/state/remaining-length triple as `prophecy_active_component` with checked obs-counter allocation/Resolve wrappers, making the intended adequacy-owned component explicit as a single value. Round 9 adds a checked component initializer and component-preserving allocation/Resolve wrappers (`prophecy_active_component_init`, `prophecy_active_component_after_alloc`, `prophecy_active_component_after_resolve`, and `prophecy_active_component_*_component`) so an adequacy owner can thread one package across both cursor bumps rather than reconstructing loose fields. Round 10 adds a checked framed active-component allocation wrapper (`prophecy_active_component_alloc_obs_ctr_component_frame`) and exposes decoder preservation from component Resolve, strengthening the singleton component for multi-token/helper-style proofs. Round 14 also exposes and checks the non-`repr` current-counter component allocation rule plus a framed current-counter allocation rule (`prophecy_active_component_alloc_current_component[_frame]`), so an already-open active component can allocate at the executable `NST.prophecy_index c` while preserving unrelated token lookups; the remaining gap is using PulseCore active adequacy to open that component instead of obtaining it from primitive witnesses

- **`Pulse.Lib.PersistentPtsTo.fst`** — `persistent_pts_to r v = ∃q. B.pts_to r #q v`
  - `make_persistent`, `dup_persistent`, `read_persistent` (erased-compatible)

- **`Pulse.Lib.Prophecy.fst`** — Typed Iris-style facade over the trusted NewProph/Resolve primitive boundary
  - `prophecy_var result payload` — opaque typed prophecy handles for atomic results and attached payloads
  - `prophecy_token p pvs` — opaque linear stream/projection token
  - `prophecy_alloc` — allocates a fresh id and existential prediction stream; no caller-supplied default
  - `resolve` — consumes a predicted head while executing one observable atomic step and returns the tail token plus `pure (x == predicted)`
  - `resolve_token` — Iris-rule form that starts from the whole stream obtained at allocation and proves it was headed by the observed result, avoiding executable branching on erased predictions

- **`Pulse.Lib.Prophecy.Trace.fst`** — Pure Iris-style observation-trace/state-interp scaffold (zero admits)
  - Models observations as `proph_id ↦ (step result, attached payload)`
  - Defines `proph_list_resolves`, allocation views, head consumption, and the coupling predicate expected from the future state interpretation
  - Defines `proph_map_interp` analogues plus verified allocation/Resolve preservation and lookup lemmas for both heterogeneous packed traces and nat-encoded observation suffixes (`proph_map_alloc_preserves_interp`, `proph_map_resolve_preserves_interp`, `proph_map_resolve_encoded_preserves_interp`, `proph_state_*_lookup`) and compact `proph_state_view` / `proph_state_view_encoded` slices tying a future trace to token streams
  - Adds verified frame-preservation lemmas for a future shared prophecy authority: fresh allocation preserves every other prophecy-map lookup, Resolve updates only the resolved prophecy id, and the compact `proph_state_*_authority_step_*` lemmas package allocation/Resolve interp, lookup, equality, and unrelated-token framing facts
  - Adds repr-level authority lemmas (`proph_state_alloc_fresh_repr_authority_step_encoded`, `proph_state_resolve_observe_repr_authority_step_encoded`, framed variants, the `repr_ctr` variants, and the Round 5 `repr_obs_ctr` variants) that combine those authority updates with the checked `NST.repr`/`NST.repr_ctr`/`NST.repr_obs_ctr` equations for `fresh_prophecy_id`/`observe`, proving allocation uses the interpreter's active prophecy cursor and Resolve consumes the interpreter's actual observation-head nat in both ordinary and counter/tape-aware adequacy shapes
  - Adds the encoded observed-head agreement and projected-tail slice (`proph_map_observed_head_agrees_encoded`, `proph_map_lookup_projected_head_encoded`, `proph_state_lookup_projected_head_encoded`, `proph_state_resolve_observed_agree_preserves_interp`) showing that, when the observation tape head decodes to the physical result and the authoritative map contains the prophecy stream, the stream head/tail shape and Resolve's `actual == predicted` equality follow from the map/trace interpretation

#### PulseCore Semantics Extension (zero admits)
- **`PulseCore.Semantics.fst`** — Added `Angel`, active prophecy-id allocation, and first-class observed-action support to computation monad `m`
  - `| Angel: decode:(nat→c) → k:(c → Dv (m a pre post)) → m a pre post`
  - `| FreshProphId: k:(pid:nat → Dv (m a pre post)) → m a pre post`
  - `| ObservedAct: decode_obs:(nat→obs) → action st b → (obs → b → Dv (m a ...)) → m a pre post`
  - `| ObservedResultAct: decode_obs:(x:b → nat → obs x) → action st b → (x:b → obs x → Dv (m a ...)) → m a pre post`
  - `step`: Angel reads from the angel oracle via `NST.angel()`; FreshProphId consumes `NST.fresh_prophecy_id()`; ObservedAct reads from the dedicated observation oracle via `NST.observe()` and runs the physical action in the same semantic step; ObservedResultAct runs the physical action then consumes/decodes one observation with access to the physical result, matching HeapLang Resolve observations
  - `mbind`, `frame`, `apply_hom`: all distribute through Angel, FreshProphId, ObservedAct, and ObservedResultAct correctly
  - `PulseCore.Semantics.observed_result_act_cont` / `PulseCore.Action.lift_observed_result_cont` / `PulseCore.Atomic.lift_atomic_observed_result_cont`: verified continuation bridge from an observable atomic action into `ObservedResultAct`, so the returned semantic reduct sees both the physical result and decoded observation before establishing the final postcondition; the non-exported `Pulse.Lib.AtomicPrimitives.lift_observed_result_cont_atomic` helper is only the current trusted-kernel compatibility counterpart used for open-invariant Resolve clients, not final native PulseCore support

- **`PulseCore.NondeterministicHoareStateMonad.fst`** — Extended with angel, observation, and prophecy-id cursors
  - Demonic tape: `nat → bool` (scheduler input to the interpreter)
  - Angel tape: `nat → nat` (ordinary existential/nondeterministic oracle input)
  - Observation tape: `nat → nat` (nat-encoded observable-step/prophecy trace input)
  - `angel()`: reads from the angel tape; `observe()`: reads from the observation tape; `fresh_prophecy_id()`: returns and bumps the active NewProph id counter; scheduler/angel/observation/prophecy-id cursors are separate, with explicit `bump_scheduler`, `bump_angel`, `bump_observation`, `bump_prophecy`, and `*_result` repr facts
  - Round 5 added `nst_obs_ctr`, `observe_obs_ctr`, and `fresh_prophecy_id_obs_ctr`, a sibling adequacy effect whose precondition and postcondition can mention the active observation tape and input/output `NST.ctr` rather than only the physical state; this is a semantics-backed trace hook with an adequacy-facing observation cursor, but not yet the full Iris state interpretation: prophecy tokens still need to be internalized as authoritative fragments over the observation trace rather than trusted primitive specs

- **`PulseCore.PartialNondeterministicHoareStateMonad.fst`** — Threaded angel and observation tapes, with Round 5 `pnst_obs_ctr` lifting for pre/postconditions indexed by observation tape and counter
- **`PulseCore.InstantiatedSemantics.fst`** — Verified unchanged

#### Examples (all verified, zero admits)
| Example | File | Key Features |
|---------|------|-------------|
| FAA via CAS | `PulseTutorial.FAAviaCAS.fst` | Canonical LA demo, `faa_is_lat`, `composed_faa` (non-trivial Φ) |
| Atomic Counter | `PulseTutorial.AtomicCounter.fst` | CAS-loop increment, `incr_is_lat` |
| Counter+Backup | `PulseTutorial.CounterWithBackup.fst` | FAA-based counter |
| Treiber Stack | `PulseTutorial.TreiberStack2.fst` | Push+Pop with persistent `is_list`, `push_is_lat`, `pop_is_lat` |
| Conditional Incr | `PulseTutorial.ConditionalIncrement.fst` | Persistent flag, `cinc_is_lat` |
| RDCSS | `PulseTutorial.RDCSS.fst` | AU spec with CAS-retry, `rdcss_is_lat`; the exported wrapper reads physical `l_m`, the main CAS path allocates/resolves a prophecy token before using the trusted Resolve equality, and descriptor-slot install plus completion/helping steps are verified as building blocks for the full Iris protocol |
| Atomic Snapshot | `PulseTutorial.AtomicSnapshot.fst` | Two-phase write, `write_is_lat`; exported `read_with` allocates a prophecy variable and resolves the middle read instead of retrying on version equality |
| Prophecy Minimal | `PulseTutorial.ProphecyMinimal.fst` | Minimal verified allocation-to-Resolve client for an atomic read, plus ghost-only shared-authority allocation/Resolve slices with explicit, counter-aware runtime, and packaged active-component observation facts, including two-token framing models over one authority and no public NewProph/Resolve witnesses |
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
2. **Dedicated observation trace hook in NST/PNST/Semantics and Atomic lifting** — `nat → nat` observation tape, `NST.observe()`, `run_alt` observation-tape parameter, `ObservedAct`, result-dependent `ObservedResultAct`, and the `Sem.observed_act` / `Sem.observed_result_act` plus `Action.stt_of_observed_action` / `Action.stt_of_observed_result_action` helpers for consuming one observation while running one physical action in the same semantic step.  The newer `Action.lift_observed_result_cont` / `Atomic.lift_atomic_observed_result_cont` bridge additionally lowers an existing observable `stt_atomic` action through `ObservedResultAct` with a continuation that can use both the physical result and decoded observation.
3. **Trusted prophecy primitive boundary with a semantics-backed allocation/Resolve slice** — the public allocation path now calls `Pulse.Lib.AtomicPrimitives.new_proph_semantic`, which consumes the active `Pulse.Lib.Core.fresh_prophecy_id`/`NST.fresh_prophecy_id` cursor and stores that fresh id in the prophecy handle, but it still allocates the public token stream locally instead of opening an adequacy-owned singleton active component.  The old pid-0 compatibility id is gone and the active-component allocation lemmas are checked, but current public NewProph remains a scaffold until that component update is moved into instantiated semantics/adequacy.  The public facade uses `resolve_proph_token_semantic` / `resolve_proph_semantic`, which frame the client atomic action, lower it through `PulseCore.Atomic.lift_atomic_observed_result_cont`, and consume one observation-tape entry in the same semantic step.  The remaining Resolve trust is still `resolve_proph_current_decode_witness`, which connects the consumed nat to the authoritative current decoded head.  The model exposes verified shared-authority/component resource slices directly; those helpers prove allocation/Resolve updates without new admits when supplied the explicit active `ot,c` premises.  The atomic-shaped `resolve_proph_token` / `resolve_proph` path retained for open-invariant clients is derived through the local `lift_observed_result_cont_atomic` observed-result `stt_atomic` boundary from the same semantic bridge; that local boundary is still trusted in `AtomicPrimitives` until PulseCore has native observed-result action support.  The next refinement is to move the singleton prophecy resource into instantiated state interpretation/adequacy and remove the public NewProph local-token scaffold plus the Resolve current-decode witness.
4. **Typed prophecy facade** — `Pulse.Lib.Prophecy.prophecy_alloc` / `resolve` no longer use split ghost refs or post-hoc ghost writes; `resolve` and `resolve_token` route through the semantic observed-result bridge rather than the legacy atomic-shaped Resolve boundary.
5. **`run_alt`** takes demonic, angel, and observation tapes
6. **Pure trace/proph-map scaffold** — `Pulse.Lib.Prophecy.Trace` records both the per-type Iris observation projection and a representation-agnostic heterogeneous `global_trace`/`proph_map_interp` model.  It now includes verified allocation and Resolve preservation lemmas plus compact packed and nat-encoded state-view models.  The nat-encoded side (`encoded_trace_of_tape`, `proph_map_interp_encoded`, `proph_state_interp_encoded`, `proph_map_resolve_encoded_preserves_interp`, and `proph_state_resolve_observed_agree_preserves_interp`) is the current shared representation between the token model and the PulseCore observation oracle.  The state-view models now also carry the next fresh prophecy id (and, for the nat-encoded view, the observation index) with verified fresh-allocation, Resolve-preservation, observed-head agreement, observation-index/tape-advance lemmas, `proph_state_runtime_matches_tape_encoded` tied to `NST.observation_index`/`NST.bump_observation`, and `proph_state_runtime_matches_ctr_encoded` tied to both `NST.observation_index` and `NST.prophecy_index`/`NST.bump_prophecy`.  The latest shared-authority lemmas also prove allocation/Resolve frame other prophecy-map entries and now have repr-level variants tied directly to `NST.repr (fresh_prophecy_id())` and `NST.repr (observe())`, which is the map/interpreter fact needed to move from per-handle state to a single authoritative resource; however this is still a verified projection model rather than an authoritative resource in active instantiated PulseCore state.
7. **Verified client paths** — `PulseTutorial.ProphecyMinimal.alloc_and_resolve_atomic_read` verifies allocation followed by Resolve, and `shared_authority_single_observation_model` verifies the witness-free resource-level path: a single shared `prophecy_authority_state` allocates a token fragment projected from a concrete future observation suffix, then resolves it with explicit observation-head facts using `prophecy_authority_resolve_observed` rather than either public boundary-local witness. `shared_authority_runtime_single_observation_model` verifies the stricter counter-aware slice: a single runtime authority tied to an active `NST.ctr` allocates using `NST.prophecy_index`, then resolves using the observation tape head at `NST.observation_index`, without calling either public boundary-local witness or passing a precomputed token tail. `shared_authority_two_observation_framing_model` extends the older explicit-fact model to two prophecy variables allocated from the same authority: resolving the first prophecy updates the shared future suffix/token map while framing the second token fragment, and the second prophecy remains resolvable from the updated authority. `shared_authority_runtime_two_observation_framing_model` proves the same two-token framing slice under the counter-aware runtime authority, deriving consecutive allocation ids from `NST.prophecy_index` and consuming concrete observation-tape heads at successive `NST.observation_index` values. `PulseTutorial.AtomicSnapshot.read_with` now uses `read_with_allocated_prophecy_step`, whose middle read is resolved by prophecy; `PulseTutorial.RDCSS.rdcss_with_m` reads a physical `l_m`, and `try_rdcss` allocates a prophecy and resolves the CAS inside the RDCSS invariant.

#### What's Still Missing: Making the Coupling First-Class
For the public facade, allocation now consumes the active prophecy-id cursor, but it still initializes the public token stream locally rather than by opening the adequacy-owned singleton prophecy component.  Resolve executes the physical atomic action and consumes a nat from the observation tape through `ObservedResultAct`, but the token-tail shape/result equality still depends on `resolve_proph_current_decode_witness`.  The model has verified first-class shared-authority/component slices that can allocate and resolve token fragments against one authoritative `proph_state_view_encoded` without new admits when the caller supplies the active `ot,c` premises; those slices are not yet wired into public `stt`/`stt_atomic` NewProph/Resolve.  The active authority is therefore still not stored as the single shared PulseCore state interpretation used by adequacy.  The heterogeneous global trace, `proph_map_interp`, and pure allocation/Resolve preservation lemmas are modeled in `Pulse.Lib.Prophecy.Trace`, but they are not yet represented as explicit shared PulseCore runtime/semantic state.

**Round-27/Round-39 implementation note.** Round 31 deleted the old pure-only `new_proph_shared_old_state_witness` and changed `new_proph_semantic` to open a trusted singleton-authority lookup, then perform the allocation by updating that authority with the verified Trace allocation lemma and `GhostFractionalTable.update`. Round 32 removed the dead pid-0 local NewProph compatibility body and added a verified counter-aware two-token shared-authority framing model; in the current tree, however, public `new_proph_semantic` still initializes its token stream locally (`[]`), so this is not yet an Iris-faithful active-component allocation. Round 34 narrowed the pure Resolve-side adequacy obligation further with current-counter repr lemmas: once a shared authority is tied to `NST.observation_index` by `proph_state_runtime_matches_ctr_encoded`, the authoritative trace head and suffix are derived from the observation tape rather than passed as separate premises. Round 35 pushed that shape into the resource-level runtime API with `prophecy_authority_resolve_current`, whose callers supply only the current-head decode fact and no longer pass the observed nat separately; the ProphecyMinimal counter-aware models use this narrower API. Round 37 moved the public token itself to hide a counter/tape-indexed runtime authority, updated public NewProph with `proph_state_alloc_fresh_authority_step_ctr_encoded`, and changed public Resolve to call `prophecy_authority_resolve_current`; the old `resolve_proph_observation_head_witness` is gone, replaced by the narrower `resolve_proph_current_decode_witness` that only connects the `ObservedResultAct` nat to the current decoded head of the token's active runtime authority. Round 39 added `prophecy_authority_alloc_runtime_frame`, a verified resource-level allocation rule that consumes the active `NST.prophecy_index` under `prophecy_authority_runtime_state` while framing an existing token fragment and proving that the existing prophecy-map lookup is preserved in the updated authoritative state; the counter-aware two-token ProphecyMinimal regression now uses this helper for the second allocation instead of re-proving preservation manually. Round 1 of the overnight audit loop added checked `repr_ctr` authority lemmas for fresh prophecy allocation and current-head Resolve, plus a ProphecyMinimal regression exercising that counter-aware shape. Round 3 named the exact shared state-interpretation slice as `prophecy_shared_state_interp` and added checked allocation/Resolve wrappers that open, update, and close that slice at `NST.bump_prophecy` and `NST.bump_observation`; this avoids reworking the authority proofs again when adequacy begins owning the slice directly. Round 4 confirmed that these wrappers are ghost/resource-level rules, not a drop-in executable replacement for public NewProph: attempting to route `new_proph_semantic` through the ghost allocation wrapper hits the expected Pulse erasure/informativeness barrier because public NewProph must return an informative `prophecy_var` while the wrapper receives the old state as erased ghost data. Round 5 added the first additive counter/tape-indexed effect seam (`NST.nst_obs_ctr`, `PNST.pnst_obs_ctr`, and `Sem.pnst_sep_obs_ctr_interp`) plus checked `repr_obs_ctr` Trace and shared-state-interp wrappers; their pre/postconditions can now own an `si ot c` resource and close it at the primitive's returned counter. Round 8 packaged the same singleton authority, encoded state, and suffix length as `prophecy_active_component`, with checked obs-counter allocation/Resolve wrappers over that package. Round 9 completed the package-threading shape by adding a checked initializer plus allocation/Resolve wrappers whose posts return `prophecy_active_component_interp (after_*) ot c'` directly, and a `ProphecyMinimal` regression that allocates and resolves while carrying the package through `NST.bump_prophecy` and `NST.bump_observation`. Round 10 adds framed allocation over the same package and exposes Resolve's decoder-preservation fact, which is needed when later helpers must keep using another prophecy's current-head decoder after an unrelated component update. Round 11 records the exact foundational authorization request in `PROPHECY_FOUNDATIONAL_CONSULTATION.md`: auditors need to approve making exactly one `prophecy_active_component_interp comp ot c` part of the active counter/tape-indexed state interpretation, adding executable NewProph and observed-result Resolve rules that open/update/close that component at the real `NST` counters, and choosing whether the private `lift_observed_result_cont_atomic` helper may remain temporarily or native observed-result `stt_atomic` support is required immediately. Round 12 removed the named `new_proph_active_runtime_authority` function and rerouted public NewProph through an informative active-component package plus a checked component allocation step; the remaining requested edit—making the active-component opening and Resolve current-decode fact come from the active `NST.fresh_prophecy_id`/`NST.observe` cursor and instantiated state interpretation rather than primitive-boundary seams—therefore no longer lacks a pre/post shape or a first-class component package, but still requires connecting the component opening/Resolve to that state interpretation.  Round 13 added `prophecy_active_component_resolve_current_component`, a checked component-level Resolve rule that consumes/returns exactly `prophecy_active_component_interp comp ot c` at `NST.bump_observation c`, and refactored the public hidden-token Resolve update to package its runtime authority as that active component before applying the checked update.  This removes another loose runtime-authority update path, but it deliberately does not claim to discharge `resolve_proph_current_decode_witness`: the typed current-head decoder fact is still supplied by that boundary until active adequacy opens the component at the `ObservedResultAct` input counter. Round 14 exposed the matching current-counter allocation rule and added a checked framed variant, so the executable NewProph path's post-open component update is now available as a first-class component rule and preserves other token fragments through the singleton component; `ProphecyMinimal.active_component_current_two_allocation_framing_model` verifies that shape. Round 15 added checked current-head projection lemmas (`proph_state_lookup_projected_current_head_encoded` and `proph_state_observed_current_head_agrees_encoded`) and refactored the runtime Resolve authority update to use that current-counter lemma: once a real active state interpretation supplies the typed decode fact at `ot (NST.observation_index c)`, the token head/tail and result agreement are now derived directly from the authoritative map interpretation without restating an explicit `n :: ks` trace-head premise. Round 16 adds the first core adequacy hook for this route: `PNST.weaken_obs_ctr_with` plus `Sem.pnst_sep_obs_ctr_interp_fresh_prophecy_id` and `Sem.pnst_sep_obs_ctr_interp_observe` package the counter facts needed to advance a caller-supplied `si ot c` index across the active `NST.fresh_prophecy_id_obs_ctr` and `NST.observe_obs_ctr` cursor steps. These hooks are checked and avoid manufacturing any resource from `emp`, but Round 17 clarified that they are pure same-state weakening hooks: their `close` obligations prove a postcondition over the same semantic state `s0`, so they cannot by themselves perform the ghost-table updates needed by `prophecy_active_component_alloc_*` or `prophecy_active_component_resolve_*`. The public prophecy primitives therefore cannot be refactored merely by instantiating those hooks with `prophecy_active_component_interp`; they need a state-changing counter-aware NewProph/observed-result Resolve rule (or equivalent adequacy runner step) that combines the cursor bump with the authoritative component update. Round 18 adds that missing generic core shape at the PNST/Semantics layer: `PNST.lift_st_then_fresh_prophecy_obs_ctr` and `PNST.lift_st_then_observe_obs_ctr` run a real state computation framed by the current `si ot c` and then close at `NST.bump_prophecy c` / `NST.bump_observation c`, while `Sem.pnst_sep_obs_ctr_interp_fresh_prophecy_id_state` and `Sem.pnst_sep_obs_ctr_interp_observed_result_state` package these as checked state-changing adequacy hooks. These hooks still are not wired into the public Pulse `stt`/`stt_atomic` prophecy primitives, and they do not by themselves delete the remaining `new_proph_active_component_open` or `resolve_proph_current_decode_witness`; they provide the reviewed runner shape needed for that next refactor without manufacturing resources from `emp`. Ordinary `NST.ens_t`/`PNST.ens_t` and `Sem.pnst_sep` clients still talk only about the physical state `s1`; the new seam is a sibling, not yet the default `Sem.state.invariant`. Therefore a faithful singleton authority cannot simply be pulled out of the hidden token table in `Pulse.Lib.AtomicPrimitives`: the primitive still needs the next counter-aware state-interpretation/adequacy connection (or an equivalent first-class Resolve/NewProph action) before the code can prove that the shared authority's `encoded_next_proph_id` and `encoded_observation_index` are the active interpreter cursors rather than trusted boundary-local facts. Round 19 records the exact remaining authorization choice in `PROPHECY_FOUNDATIONAL_CONSULTATION.md`: the next implementation patch must either introduce prophecy-specific semantic NewProph/Resolve actions over the singleton component or extend ordinary `stt`/observed-result adequacy so the Round-18 state-changing hooks can be instantiated directly, and auditors must explicitly choose whether the private observed-result atomic compatibility helper may remain temporarily or native observed-result `stt_atomic` support is required now.

In Iris, this coupling lives in the **state interpretation**:

- Iris's `state_interp σ κs` receives the full observation trace `κs` (universally quantified in adequacy)
- `proph_map_interp κs ps` seeds a ghost map from `κs`
- `proph p pvs` is a ghost map fragment — user gets `pvs = proph_list_resolves κs p`
- At `Resolve`, ghost map update proves `pvs = (result, tag) :: pvs'`
- The equality is a CONSEQUENCE of ghost map agreement, not an axiom

#### How to Continue in Pulse

The current implementation chooses the conservative trusted-boundary route first: expose Iris-shaped NewProph/Resolve rules to clients while keeping the heterogeneous observation trace abstract inside `Pulse.Lib.AtomicPrimitives`.  Round 6 added the first core semantic hook for that trace (`ObservedAct` + observation tape), and the public Resolve path now uses the result-dependent observation bridge to consume an observation in the same semantic step as the wrapped atomic action.  The latest Round 6 edit additionally factors the open-invariant Resolve wrapper through a local non-exported observed-result `stt_atomic` compatibility helper (`lift_observed_result_cont_atomic`) instead of directly casting the full Resolve rule.  Remaining foundational work is narrower but still decisive: allocation still uses a local token-stream scaffold instead of opening an adequacy-owned active component, Resolve still trusts the final current-decode fact for the consumed observation, and both facts need to come from a first-class state-interpretation/adequacy resource rather than boundary-local seams.  The local observed-result atomic helper is still implemented by the trusted primitive-kernel coercion, so native PulseCore support remains required before this can be called the final open-invariant Iris rule (unless auditors explicitly approve keeping this scoped seam temporarily).  The concrete consultation/design for that foundational edit is tracked in `PROPHECY_FOUNDATIONAL_CONSULTATION.md`.

1. **Extend the instantiated state/adequacy interpretation** (`Sep.full_mem` plus a sibling counter/tape-indexed state interpretation, or a product state) with the first-class observation suffix, observation index, next fresh prophecy id, and authoritative token map whose pure shape is now captured by `Pulse.Lib.Prophecy.Trace.proph_state_view_encoded`.
2. **Expose a counter/tape-indexed invariant seam**.  The current `state.invariant : s -> pred` and ordinary `stt` postconditions cannot mention the active `NST.ctr` or observation tape.  The next API must let the prophecy component own `prophecy_authority_runtime_state auth st ot c len` at the same `ot`/`c` used by `FreshProphId` and `ObservedResultAct`.
3. **Refine `new_proph_semantic` further** from active fresh-id allocation plus local token-stream initialization into an action over the shared active authoritative prophecy state, exposing the actual projection of the current/future observation list for the freshly allocated id across all prophecy handles without a primitive-boundary seam.
4. **Refine the remaining Resolve current-decode witness** from the current trusted `resolve_proph_current_decode_witness` boundary into an action over a shared authoritative prophecy state.  The public semantic Resolve path already runs the physical step and consumes an observation during that step; what remains is opening the singleton active state interpretation at that same input counter and proving the consumed nat is the authoritative current head via that state interpretation instead of trusting the witness.
5. **Adequacy/run semantics** must quantify/thread the observation list consistently with actual Resolve observations; the current observation tape and `run_alt_with_ctr` result are hooks, but adequacy still has to connect them to `proph_map_interp` and actual Resolve emissions through a counter-aware resource, not through token-local witnesses.
6. **Strengthen clients from Resolve equality to full Iris protocols** only after the core seam is discharged: the allocation-to-Resolve client rule now exists as `resolve_token`, and RDCSS clients no longer pass a pure `m_val`; however AtomicSnapshot still needs the original Iris pointer-indirection write/AU proof and RDCSS still needs invariant-managed shared `l_m`, descriptors, helping, and prophecy-based LP identification across helpers.

Key files for that deeper refinement:
- `PulseCore.InstantiatedSemantics.fst` — extend `state0` to include observation state
- `PulseCore.MemoryAlt.fsti/fst` or a new prophecy memory module — define `proph_map_interp`
- `PulseCore.Semantics.fst` / `PulseCore.Action.fst` / `PulseCore.Atomic.fst{i}` — the generic `ObservedResultAct` continuation bridge now exists and Round 20 names the explicit semantic helper as `Sem.observed_result_act_cont`; the remaining work is to specialize it into a first-class `resolve_action` over an authoritative prophecy state that consumes the observation head and updates the token map, and then expose an atomic form accepted by `with_invariants` rather than by the private compatibility coercion
- `PulseCore.PartialNondeterministicHoareStateMonad.fst{i}` / `PulseCore.Semantics.fst` — Round 16 adds checked obs-counter weakening and cursor-step hooks (`PNST.weaken_obs_ctr_with`, `Sem.pnst_sep_obs_ctr_interp_fresh_prophecy_id`, and `Sem.pnst_sep_obs_ctr_interp_observe`) so adequacy proofs can expose the real `FreshProphId`/`observe` counter facts by an explicit caller-supplied close proof instead of an implicit `emp` witness; Round 17 documents that these hooks are same-state weakenings; Round 18 adds checked state-changing siblings (`PNST.lift_st_then_fresh_prophecy_obs_ctr`, `PNST.lift_st_then_observe_obs_ctr`, `Sem.pnst_sep_obs_ctr_interp_fresh_prophecy_id_state`, and `Sem.pnst_sep_obs_ctr_interp_observed_result_state`) that can run an authoritative-component update while advancing the active counter
- `Pulse.Lib.AtomicPrimitives.fst` — replace the admitted prophecy model once first-class semantics exist

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
| Prophecy coupling | Pure heterogeneous trace/proph-map model exists and clients use the trusted Resolve equality; still missing first-class state-interpretation/adequacy extension | The main remaining work |
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
