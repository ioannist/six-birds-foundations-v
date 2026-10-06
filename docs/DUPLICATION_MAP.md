# Duplication map: Foundations V results against the earlier corpus

Method. (1) Every corpus paper available in the companion `six-birds-papers`
source collection was searched for the vocabulary of each D/E unit
(case-insensitive regular expressions over the full TeX source; the query list
is in §3). That collection contained 53 papers and did not include this
manuscript. (2) Every hit was read in context and classified as *canonical
home* (the result is stated there), *component source* (a hypothesis,
predicate, or theorem that this paper imports as a certified input or
applies), *recognition source* (named in the paper as motivation only), or
*false positive* (vocabulary overlap without a result). (3) For each
Foundations V result the earliest corpus statement of any recovered component
was located and its identifier recorded (theorem/lemma/proposition/definition
number as rendered by that paper's own counters, computed from its
`\newtheorem` declarations, plus the source label). (4) Two sibling papers
cited by the manuscript were not in that collection: Foundations VI
(manuscript, forward pointer only) and the Life paper *To Wake a Stone with Six
Birds* (Zenodo 10.5281/zenodo.18420406). For those the entry says "canonical
source not in repo".

Labels used below are the provenance vocabulary of the audit: RECOVERED STANDARD, RECOVERED SBT, ELEMENTARY, SHARPENED, NEW.

## 1. Canonical homes of every recovered component

| Component used in this paper | Canonical corpus statement | Vendored Lean (if any) | Relation of this paper's use |
|---|---|---|---|
| Theory package `(Z,f,Σ_f,E,𝒜)` | Foundations I, Definition 1 (Finite theory package), label `def:tk-theory-package` | authored `SixBirdsFoundationsV.TheoryPackage` (Z arbitrary) | differently scoped: finiteness by scope, not by type |
| Six primitive roles P1–P6 | Foundations I §10.1 (Definitions of P1–P6); Foundations II §2 (repaired role meanings) | — | identical reading, restricted to P1–P5 as repair sorts |
| Split-pair obstruction `Δ(q,F,r)`, descent iff empty, source-refinement / target-coarsening repairs | Foundations IV Theorem F2 (Descent-Repair Normal Form), `thm:F2` | — (E4 uses an `F2Certified` interface) | identical statement, used as certified input |
| Current vs predictive quotient, predictive witness | Holonomy with Memory Definitions 2.1–2.4; Foundations IV Theorems F3 (Holonomy-Memory Repair Normal Form) and F13a (Hiddenness Normal Form) | `HolonomyMemory.*` (corrected core) | identical; E16 applies Theorem 3.6 verbatim |
| Closure deficit `CD_τ` | Foundations III Theorem 8 (FiniteMarkovClosureDeficit) | — | identical notation, used as a rational score |
| Adequacy residual `Ξ_C(D|L)`, chain rule, same-family saturation, blind-spot witness | Xi paper Definition 4.2 (Adequacy residual), Theorem 8.2 (Chain rule), Corollary 8.3 (Same-family saturation), Theorem 10.2 (Blind-spot witness), Definition 10.1 (declared residual budget) | `Xi.AdequacyResidual`, `Xi.Obstruction` | D2/E9 take the chain-rule identity as a hypothesis (weaker); E7 uses the witness predicate as a certified input |
| Currency, shadow price, slack collapse, proxy-currency failure | Currency paper §2.3 (strict definition of currency: a map u:Y→R^k under four structural conditions), §2.4 (proxies), §3.2 (shadow prices as higher-layer currencies), §5.2 (price emergence and slack), §5.4 (proxy currencies fail) | — | §2 abridges the definition to a carried, declared-role notion (differently scoped); E6/E8 recover the shadow-price reading; the finite-Markov evidence of that paper is not reused |
| Viability kernel as greatest fixed point; schedule trap; agenthood vs agency | Agents paper §3.5, §5.2, §1.3 and the Lean anchor of its §12 | — | certified inputs / comparator vocabulary |
| Institution as strict extension; formation/formed; washout; material forcing; coercion-null | Institutions paper Propositions 5.5, 6.1, 6.2, 6.3, 6.5 | — | E11 uses 6.2/6.3 as certified host inputs; E13.3 is a verification wrapper on a certified null of the shape of 6.5 |
| Same-level self-audit failure; finite rotating audit | Foundations III Theorem 24 (SameLevelSelfAuditFailure), Theorem 25 (FiniteRotatingAudit); Foundations IV Theorem F21 (Reflexive Nonclosure) | `SixBirdsIII.InstrumentClaims`, `SixBirdsIII.RotatingAudit` | E2's `E2_SelfSoundnessObstruction` evaluates the vendored classifier restricted to a carried level and concludes only `classify ≠ accepted`: weaker than Theorem 24 (which also fixes the `outside_scope`/`undefined_circular` dichotomy) and weaker than the four-clause F21 |
| Top-down channel vs structural downward path; NC-TD | Foundations III §4.7 (Structural Downward Influence Versus Top-Down Causal Channels) and nonclaim NC-TD (§16) | `SixBirdsIII.TopDownChannel` | `E11_NCTDObstruction` reuses the vendored witness (identical); E4/E10/E11 take channel records as certified inputs |
| Promotion-gate soundness | Foundations III Theorem 19 (PromotionGateSoundness) | `SixBirdsIII.Promotion` | E4 projects through it (`compilationLawful_requiredCoreGatesPass`) |
| Source-of-truth tag set (`committed_state`, …, `fallback`, `unknown`, `contradictory`) | Foundations III §4 (Source, Provenance, and Audit Records; `SourceOfTruth`) | — (authored `CarriedSource` re-declares the tags) | identical tag set; D3 adds generation/scope flags |
| Strict extension | Foundations IV Lemma F8 (Strict Extension), `lem:F8` | — | D6/E4 saturation test is the Xi Corollary 8.3 instance |
| Sufficiency closure; quotientality | Foundations IV Theorems F7, F10 | — | E12 certified inputs |
| No Unstatused Residual; Fact/Record Formation; Object Persistence | Foundations IV Theorems F9, F20, F19 | — | E3/E7/E14 certified inputs |
| No-Free-Distinction; Adequacy/No-Overread | Foundations IV Theorems F12, F11 | — | E1/E6/E7 certified inputs |
| Interface Mediation; Presentation Invariance; Objectivity as Common Quotient | Foundations IV Theorems F22, F29, F17 | — | E13 certified inputs; E12.1 recognition |
| Finite forcing lemma | Foundations I Theorem 6 (Finite forcing lemma / physical forcing lemma), `thm:finite-forcing` | — | E1 strictness certificate (`E1_StrictSelfExtension` takes it as input) |
| KKT conditions, complementary slackness, shadow-price reading, local sensitivity | Boyd & Vandenberghe 2004 §5.5.3 (pp. 243–244), §5.5.2 (pp. 242–243), §5.4.4 (pp. 240–241), §5.6.3 (p. 251) | — | E6 Lean takes a KKT witness as hypothesis (weaker); E8 envelope identity is paper-level only |
| Loop asymmetry (current-trivial, predictively nontrivial loop) | Holonomy with Memory Theorem 3.6, `thm:loop-asymmetry`; Lean `loopAsymmetry_exhibits_movedPredictive_fixedCurrent` | `HolonomyMemory.Asymmetry` | `E16_LoopAsymmetryAnchor` applies it verbatim (identical) |
| Five open boundaries answered by the catalog | Foundations II §11.3 (The endogenous-instrument meta-limit); Reflexive SBT §9.3 (Open problems and the next paper), paragraph "(F3) Reflexive capacity contraction theorems"; Needle Killer §9 (Discussion), "quantitative theory of probe-family enlargement"; Currency paper §3.5 (Relation to PICA: the P6 ← P6 cell, "accounting regulates itself") and §6.1 (attention weights as prices); Institutions paper §10 (Discussion, scope, and outlook; "within-agent learning or acquisition carrier") and §1 ("history-dependence grows with experience") | — | recognition sources; correctly attributed in §1 and §9 |
| Life-facing finite evidence (§11 tables) | Life paper (canonical source not in repo); claim-ledger identifiers from that project's `assets/claims.yml` | — | transcribed numbers; no theorem |

## 2. Per-result verdicts

| Result | Prior corpus home? | Verdict |
|---|---|---|
| Definition 2.1 (theory package) | Foundations I Definition 1 | RECOVERED SBT; differently scoped |
| Definition 2.2 (six-part normal form) | Foundations IV normal-form template | RECOVERED SBT (presentation convention) |
| D1 Repair join (Def. 3.1) | source refinement in F2; the join symbol is not defined in the corpus (`repair join` has 0 corpus hits) | SHARPENED (typed record of F2's source-refinement move); meet of partitions is ELEMENTARY |
| Prop. 3.7 (semilattice laws) | none | ELEMENTARY |
| D2 Predictive surplus (Def. 3.2) | CD (FIII Thm 8), Ξ (Xi Def. 4.2); the scalar `S_τ` is not in the corpus | SHARPENED (scalarization of recovered quantities) |
| Prop. 3.8 | Xi Thm 8.2, Cor. 8.3 for the operator clauses | RECOVERED SBT (operator clauses, weaker: identity taken as hypothesis) + ELEMENTARY (rational clauses, trace monotonicity) |
| D3 Carried record (Def. 3.3) | FIII source tags; "carried record" has 0 corpus hits | SHARPENED (typed record over FIII tags with generation, scope, coordinate, own-kernel trace) |
| Prop. 3.9 | none | ELEMENTARY (disjoint constructors) |
| D4 E-system (Def. 3.4) | 0 corpus hits for "E-system"/"endogenous closure" | NEW (definition); components RECOVERED SBT |
| Def. 3.10, Prop. 3.11 | none | SHARPENED / ELEMENTARY |
| D5 Closed-loop scope (Def. 3.5) | 0 corpus hits | NEW (definition) |
| Prop. 3.12 | none | ELEMENTARY |
| D6 Probe economy (Def. 3.6) | Hiddenness paper Definition 5.1 (Visibility coupling / exposure); Xi Cor. 8.3; "probe economy"/"exposure budget" 0 hits | SHARPENED (priced, carried version of the Hiddenness exposure predicate) |
| Prop. 3.13 | Xi Cor. 8.3 (clause 4) | ELEMENTARY + RECOVERED SBT |
| E1 (Thm 5.1) | no corpus statement ("internalization" hits are unrelated: strict-test/carrier papers use it for internalizing protocol phase) | NEW; RECOVERED SBT components (F2, F12, FI Thm 6, FIII Thm 19, FIII tags) as certified inputs; SHARPENED exact five-way characterization |
| E2 (Thm 5.2) | self-soundness clause: FIII Thm 24 / FIV F21; stratification: FIII Thm 25 | RECOVERED SBT (weaker: not-accepted conclusion only, carried-level restriction) for clause 1; RECOVERED SBT (weaker) for clause 2; ELEMENTARY capacity bound; NEW status partition |
| E3 (Thm 5.3) | "self-maintain/reclosure" hits only in Lean declaration names of unrelated Clay-problem papers | NEW; RECOVERED SBT components (FIV F19, F20 consumed as hypotheses, weaker) |
| E4 (Thm 5.4) | none ("compilation" hits are Lean/compiler vocabulary elsewhere) | NEW; RECOVERED SBT components (FIII §4.7 channel, Thm 19, F8, Xi Cor. 8.3, F2) |
| E5 (Thm 5.5) | none ("collapse" hits are unrelated: witness collapse, wave-function collapse, defect collapse) | NEW; falsifier ELEMENTARY |
| E6 (Thm 6.1) | KKT/slack: Boyd & Vandenberghe; currency reading: Currency paper | RECOVERED STANDARD (weaker Lean form) + RECOVERED SBT + SHARPENED (genuine-scarcity scope repair) |
| E7 (Thm 6.2) | Xi Thm 10.2 witness; "alarm" 0 corpus hits | NEW; RECOVERED SBT components |
| E7.1 | repository catalog only | NEW, interpretation-grade, unformalized |
| E8 (Thm 6.3), E8.1 (Cor. 6.4) | Currency paper §3.2/§5.2/§5.4; B&V §5.6.3; Xi Def. 10.1 | RECOVERED STANDARD (paper-level envelope identity) + RECOVERED SBT + NEW (seven-way classification; capture corollary) |
| E9 (Thm 6.5) | Xi Thm 8.2/Cor. 8.3; Needle Killer open problem; "curiosity" 0 relevant hits | ELEMENTARY (finite argmax) + RECOVERED SBT (identical content of Cor. 8.3 for the trace discharge, weaker form) + NEW (arbitration record) |
| E10 (Thm 6.6), E10.1, E10.2 | FIII §4.7/NC-TD; Agents §1.3/§5.2 | NEW; RECOVERED SBT components |
| E11 (Thm 7.1) | FIII NC-TD (identical reuse in `E11_NCTDObstruction`); Institutions Props 6.2/6.3 as host inputs; "stack-active" 0 hits | NEW (partition and comparators) + RECOVERED SBT |
| E11 countermodels | none | SHARPENED (minimized falsifiers; computed receipts) |
| E12 (Thm 7.2) | F7/F10/F17; Agents §3.5; "individuation" 0 hits | NEW; RECOVERED SBT components |
| E12.1 (Rem. 7.3) | FIV F17 turned inward | NEW, interpretation-grade, unformalized |
| E13 (Thm 7.4), E13.1–E13.4, Prop. 7.9 | Institutions Prop. 6.5 (coercion-null); F22/F29; "repair transport"/"teaching" 0 relevant hits | NEW; RECOVERED SBT components (E13.3 differently scoped from Prop. 6.5) |
| E14 (Thm 8.1) | F9/F20 certified; Holonomy/F3 background; "reconsolidation/retrieval" 0 hits | NEW; RECOVERED SBT components (FIV F9, F20 consumed as hypotheses, weaker) |
| E15 (Thm 8.2–8.13) | F3 residue status and Xi Def. 4.2 residual as certified inputs; the P2 role is the Foundations I §10.1 / II §2 primitive (Foundations III's role gloss is informal); "offline/closure debt" 0 hits | NEW; RECOVERED SBT components (FIV F3, Xi Def. 4.2 consumed as records, weaker; P2 role label identical); Prop. 8.5 ELEMENTARY |
| E16 (Thm 8.14–8.29) | Holonomy Thm 3.6 (Prop. 8.26 identical application); F3/F13a; "adaptability" hits unrelated (Currency §2.3 route-dependence caveat) | NEW; Prop. 8.26 RECOVERED SBT; Props. 8.27–8.29 SHARPENED |
| Appendix C entries | as above per unit | NEW/SHARPENED exclusion projections; `E11_NCTDObstruction` RECOVERED SBT; `E6_SlackCollapse` RECOVERED STANDARD (weaker); `E9_SameFamilyStrictness` RECOVERED SBT; `E4_Brittleness` RECOVERED SBT instance of F2 |

## 3. Sweep queries and hit counts (53 corpus files)

Each query is a case-insensitive Python regular expression over the full TeX source of every file in the checkout. Counts are files, not occurrences.

| Query | Files hit | Disposition |
|---|---|---|
| `E-system\|endogenous closure` | 2 (Foundations IV; To Flatten a Stone) | both false positives: the substring `e-system` inside hyphenated words such as `role-system`; neither states an E-system |
| `repair join`, `carried record\|carried instrument`, `closed-loop scope`, `probe economy\|exposure budget`, `bounded reflexivity\|audit tower`, `institutional rewrite\|stack-active\|stack activity`, `individuation\|individuality`, `reconsolidation\|retrieval` | 0 | no prior home |
| `internali[sz]ation` | 8 | all refer to internalizing protocol/phase variables or hidden lifts (Hiddenness Lift D "planted-suppressed internalization"); none states E1 |
| `self-maintain\|reclosure` | 2 (Clay-problem papers) | Lean declaration names only |
| `compilation\|compiled repair\|habit` | 10 | compiler/Lean vocabulary; Institutions "habit" is not a law |
| `collapse` | 48 | unrelated senses (witness collapse, wave-function collapse, defect collapse) |
| `attention` | 5 | Currency paper (attention weights as prices: recognition for E6); Language paper (transformer attention); Foundations III ("restricts attention") |
| `alarm` | 1 (Foundations IV) | vocabulary only; no result |
| `shadow price\|control price` | 3 | Currency paper (recognition/component for E8); others unrelated |
| `curiosity\|probe acquisition` | 1 (Neutrino) | "parameter-level curiosity", unrelated |
| `cognitive demarcation\|intention\|goal` | 38 | generic words; no demarcation law |
| `repair transport\|teaching\|communication` | 4 | no-signalling / communication cost, unrelated |
| `offline\|sleep\|closure debt` | 1 | unrelated |
| `adaptability\|trained immunity\|route-dependent` | 5 | Currency §2.3 caveat; Lay-a-Stone holonomy; none states E16 |
| `Foundations V\b\|endogenous` in Foundations IV | 0 | Foundations IV does not anticipate the catalog |

Per-file hit lists are reproducible from the queries above; the audit's scratch record (`sweep.json`) was generated on 2026-09-02.

## 4. Sibling papers not in the checkout

- **Foundations VI**: cited only as the forward seam (`tab:series-position`). No result of this paper is attributed to it. Canonical source not in repo.
- **Life paper** (`Tsiokos2026Life`): §11 transcribes its executed numbers and claim-ledger identifiers, and §13/§14 cite its nonclaims. No theorem of this paper is recovered from it. Canonical source not in repo; the numbers were compared against the sibling repository's `paper.tex` and `assets/claims.yml` read-only (Phase 3).
