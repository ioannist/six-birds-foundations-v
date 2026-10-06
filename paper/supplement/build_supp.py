#!/usr/bin/env python3
"""Generate the supplement tables of Foundations V from the Lean sources, the
theorem catalog THEOREMS.md, the dated axiom receipt and
the instance axiom transcript.  Run from the repository root:

    python3 paper/supplement/build_supp.py

Nothing is typed by hand except the map from main-paper items to their entry and
Lean declarations (ITEMS below) and the status each entry has in the paper
(PAPER).  Every file and line number is read from the sources; a declaration
that cannot be found, or a theorem without an axiom record, stops the script.
"""
import re, pathlib, sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
LEAN = ROOT / "lean"
OUT = pathlib.Path(__file__).resolve().parent

# ---- Lean declarations -------------------------------------------------------
DECL = re.compile(r"(?:noncomputable |protected |private )*(theorem|lemma|def|structure|inductive|abbrev|instance)\s+([^\s:({\[]+)")
DECLS = {}
for f in sorted((LEAN / "SixBirdsFoundationsV").rglob("*.lean")):
    rel = f.relative_to(ROOT).as_posix()
    stack = []
    for i, line in enumerate(f.read_text().splitlines(), 1):
        m = re.match(r"namespace (\S+)", line)
        if m:
            stack.append(m.group(1))
            continue
        m = re.match(r"end (\S+)\s*$", line)
        if m and stack and m.group(1) == stack[-1]:
            stack.pop()
            continue
        m = DECL.match(line)
        if m:
            fq = ".".join(stack + [m.group(2)])
            DECLS[fq] = (m.group(1), rel, i)

# ---- Catalog: entry headings in THEOREMS.md ----------------------------------
CAT = {}
for i, line in enumerate((ROOT / "THEOREMS.md").read_text().splitlines(), 1):
    m = re.match(r"### (E\d+)\. (.*)", line)
    if m:
        CAT[m.group(1)] = {"name": re.sub(r"\s*\(.*$", "", m.group(2)).replace("*", "").strip(), "line": i}
    m = re.match(r"\*\*(D\d) \(([^)]*)\)", line)
    if m:
        CAT[m.group(1)] = {"name": m.group(2), "line": i}


# ---- Axioms: dated receipt for the library, transcript for the instances ------
AX, SRC = {}, {}
for line in (ROOT / "docs" / "LEAN_AXIOM_RECEIPT.md").read_text().splitlines():
    m = re.match(r"\| `([^`]+)` \| ([^|]+) \|$", line)
    if m:
        AX[m.group(1)] = m.group(2).strip()
        SRC[m.group(1)] = "2 Sep 2026"
transcript = (OUT / "instance_axioms_2026-09-26.txt").read_text()
for m in re.finditer(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])", transcript, re.S):
    AX[m.group(1)] = "none" if m.group(3) is None else ", ".join(a.strip() for a in m.group(3).split(","))
    SRC[m.group(1)] = "26 Sep 2026"


def tex(s):
    for a, b in [("&", "\\&"), ("%", "\\%"), ("#", "\\#"), ("_", "\\_")]:
        s = s.replace(a, b)
    return s


V = "SixBirdsFoundationsV."
I = V + "Instances."
S12 = I + "E12Semantic."
S13 = I + "E13Semantic."

# Main-paper numbered items -> (entry, role, Lean declarations).  An empty list
# means the item is argued on paper only.
ITEMS = [
    ("def:theory-package", "setting", "definition", [V+"TheoryPackage"]),
    ("def:d1", "D1", "definition", [V+"Refines", V+"FiberEquiv", V+"repairJoin"]),
    ("prop:d1", "D1", "general theorem", [V+"join_refines_left", V+"join_refines_right", V+"vee_greatest_lower_bound", V+"join_idem", V+"join_comm", V+"join_assoc", V+"join_well_defined"]),
    ("def:d2", "D2", "definition", [V+"predictiveSurplusValue", V+"predictiveSurplusXi"]),
    ("prop:d2", "D2", "conditional general theorem", [V+"predictiveSurplusValue_nonnegative_iff", V+"predictiveSurplusValue_identical", V+"predictiveSurplusValue_exact_baseline", V+"predictiveSurplusXi_nonnegative_of_psd", V+"predictiveSurplusXi_chain_rule_monotone", V+"predictiveSurplusXi_same_family_saturation"]),
    ("def:d3", "D3", "definition", [V+"FineSourceTag", V+"CarriedSource", V+"CarriedRecord", V+"CarriedInstrument"]),
    ("lem:d3", "D3", "consistency lemma", [V+"not_carriedSource_fallback", V+"not_carriedSource_independent_pair_witness", V+"not_carriedSource_simulation_trace", V+"not_carriedSource_ablation_record", V+"not_carriedSource_unknown", V+"not_carriedSource_contradictory", V+"not_carriedRecord_of_step_not_in_scope", V+"not_carriedInstrument_of_incomplete_inventory"]),
    ("def:d4", "D4", "definition", [V+"RepairSort", V+"CarriedLedger", V+"RepairMove", V+"ActiveCarriedInstrument", V+"ESystem"]),
    ("def:d4-step", "D4", "definition", [V+"LawfulRepairStep", V+"ESystem.RepairStep"]),
    ("lem:d4", "D4", "consistency lemma", [V+"lawfulRepairStep_requires_detection", V+"lawfulRepairStep_requires_gate", V+"lawfulRepairStep_requires_kernel_transition", V+"lawfulRepairStep_requires_reaudit", V+"not_lawfulRepairStep_without_detection", V+"not_lawfulRepairStep_without_gate", V+"not_lawfulRepairStep_without_kernel_transition", V+"not_lawfulRepairStep_without_reaudit", V+"no_repairSort_p6"]),
    ("def:d5", "D5", "definition", [V+"ChallengeEpisode", V+"ChallengeHistory", V+"ClosedLoopScope"]),
    ("lem:d5", "D5", "consistency lemma", [V+"closedLoopScope_complete", V+"closedLoopScope_entry_carried", V+"not_closedLoopScope_of_listed_source_fallback", V+"not_closedLoopScope_of_listed_source_unknown", V+"not_closedLoopScope_of_listed_source_contradictory", V+"not_closedLoopScope_of_listed_generatedByS_false", V+"not_closedLoopScope_of_listed_inScope_false", V+"fallback_entry_cannot_borrow_carriedness"]),
    ("def:d6", "D6", "definition", [V+"ProbeEconomy", V+"SameFamilySaturated", V+"AcquisitionStrict", V+"LawfulAllocation", V+"LawfulAcquisition", V+"LawfulRetirement"]),
    ("lem:d6", "D6", "consistency lemma", [V+"lawfulAllocation_no_new_active_probe", V+"lawfulAcquisition_requires_acquisitionStrict", V+"lawfulRetirement_requires_active", V+"lawfulRetirement_probe_absent_after", V+"not_lawfulAcquisition_of_sameFamilySaturated", V+"xi_sameFamilySaturated_not_acquisitionStrict"]),
    ("def:device", "E3, E2", "instance data", [I+"eventTheory", I+"eventPolicy", I+"eventInstrument", I+"eventSystem"]),
    ("prop:device-step", "D4", "instance", [I+"eventAt", I+"eventCarried", I+"eventRepair"]),
    ("def:episode-linked", "E3", "definition", [V+"MaintenanceReinstatementFor", I+"EpisodeLinkedReinstatement", I+"FullyHistoryLinkedReinstatement"]),
    ("thm:e3-episode", "E3", "instance", [I+"eventTrajectory", I+"eventTransition", I+"eventHistory", I+"eventApp", I+"eventMaintenance", I+"eventReinstatement", I+"eventE3Reinstatement", I+"eventHistoryAgrees", I+"eventFullyHistoryLinked", I+"eventExecutedReinstatement", I+"noEpisodeLinkedWithEmptyHistory"]),
    ("def:declared-measure", "E2", "definition", [V+"CarriedInstrumentLevel", V+"CarriedInstrumentLevelOccurrence", I+"DeclaredCapacityMeasure", I+"DeclaredOccurrence", I+"DeclaredFootprint"]),
    ("thm:e2-declared", "E2", "general theorem", [I+"declaredRecordList_nodup", I+"declaredRecordList_subset", I+"declaredRecordList_length", I+"declaredCapacityBound", I+"declaredTowerCapacityBound", I+"copiedRecordReindexNotDeclared"]),
    ("thm:e2-tower", "E2", "instance", [I+"eventCheckedSystem", I+"eventCheckedSystemRepair", I+"eventInspectLower", I+"eventLowerInspectionPasses", I+"eventUpperRecordedCheck", I+"eventCheckedMeasure", I+"eventCheckedTowerAuditsLowerStack", I+"eventCheckedLevelsDisjoint", I+"eventCheckedConcreteCapacity", I+"eventCheckedCapacityBound", I+"eventCheckedStatusSaturated", I+"eventCheckedExecutedRepair"]),
    ("prop:e2-self", "E2", "imported, weaker form", [V+"E2_SelfSoundnessObstruction"]),
    ("prop:e2-v1-vacuous", "E2", "revision note: version-1 measure vacuous", [V+"AuditTowerCapacityMeasure", V+"E2_CapacityBound", I+"noE2WithOccurringLevel", I+"spikeNoE2"]),
    ("thm:e6-kkt", "E6", "general theorem", [V+"KKTWitness", V+"GenuineScarcity", V+"E6_AttentionKKT", V+"E6_SlackCollapse"]),
    ("thm:e6-caps", "E6", "general theorem", [I+"weightedCappedObjective", I+"cappedFeasible", I+"saturatedSlope", I+"weightedSaturatedSupportingPlane", I+"CapMultiplierKKT", I+"capMultiplierKKT_sufficient"]),
    ("thm:e6-atcap", "E6", "numerical instance", [I+"capExampleKKT", I+"capExampleSlopeZero", I+"capExampleGloballyOptimal", I+"unitCapExampleGloballyOptimal"]),
    ("def:e1-forcing", "E1", "definition", [I+"ActualFamilyForcing", V+"GenericallyNovelChallenge", V+"StrictSelfExtension", V+"InfinitelyManyStrictSelfExtensions"]),
    ("prop:e1-forcing", "E1", "general theorem", [I+"actualFamilyStrictExtensions"]),
    ("thm:e1-clocked", "E1", "instance", [I+"clockedTheory", I+"clockedSystem", I+"clockedInstalls", I+"clockedOddRepair", I+"clockedEvenPerturbation", I+"clockedFamilyEveryEntryInstalled", I+"clockedUnbounded", I+"periodicNovel", I+"periodicStrictAt", I+"clockedForcing", I+"clockedStrictExtensions", I+"periodicRefinementsDistinct"]),
    ("prop:e1-v1-vacuous", "E1", "revision note: version-1 certificate uninhabited", [V+"FiniteForcingStrictnessCertified", V+"E1_StrictSelfExtension", I+"finiteForcingNoPerpetualNovelty", I+"finiteForcingUninhabited", I+"E1_StrictSelfExtension_noCertificate"]),
    ("def:e12-setting", "E12", "definition", [S12+"PartClosure", S12+"System", S12+"RepairClosed", S12+"SelfMaintaining", S12+"Candidate", S12+"Maximal", S12+"Integrated"]),
    ("prop:e12-structure", "E12", "general theorem", [S12+"repairClosed_inter", S12+"integrated_disjoint_or_equal"]),
    ("thm:e12-repair", "E12", "instance", [S12+"genuineRepairClosure", S12+"repairSystem", S12+"repairPart_integrated", S12+"repairedIndividualWitness", S12+"healthyOnly_closure_loadBearing"]),
    ("prop:e12-overlap", "E12", "negative instance", [S12+"secondSystem", S12+"secondLeft_maximal", S12+"secondRight_maximal", S12+"second_no_integrated"]),
    ("def:e13-transport", "E13", "definition", [S13+"System", S13+"Interface", S13+"RepairTransport"]),
    ("thm:e13-chain", "E13", "general theorem", [S13+"compose", S13+"compose_payment", S13+"RepairChain", S13+"chain_obstruction_bound", S13+"chain_length_bound"]),
    ("thm:e13-cross", "E13", "instance", [S13+"crossTransport", S13+"cross_context_zero_to_one", S13+"cross_context_one_to_zero", S13+"cross_context_two_step_bound", S13+"sourceToReceiver", S13+"receiverToThird", S13+"concrete_composite_payment", S13+"concrete_composite_reduces"]),
    ("prop:e13-flat", "E13", "negative instance", [S13+"roleOnlyInterface", S13+"roleOnly_mapsRepair", S13+"roleOnly_no_reduction"]),
    ("ex:e6-nonconcave", "E6", "counterexample", []),
    ("rem:e6-unlinked", "E6", "counterexample", []),
    ("prop:e6-sufficient", "E6", "sufficiency, argued on paper", []),
    ("thm:e9", "E9", "general theorem", [V+"E9_CuriosityArgmax", V+"E6_E9_AccessArbitration", V+"E6_E9_AccessArbitration_epsilon", V+"selected_access_move_ratio_bound", V+"selected_access_move_ratio_bound_epsilon"]),
    ("prop:e9-saturation", "E9", "general theorem", [V+"XiAcqDischarge", V+"E9_SameFamilyStrictness"]),
    ("prop:e15-identity", "E15", "general theorem", [V+"DerivedOfflineBudgetGeometry", V+"kappaOn", V+"kappaOff", V+"freedAllocation", I+"offlineCapacityFromExhaustion", I+"geometryCapacityFromExhaustion"]),
    ("prop:e4-brittle", "E4", "general theorem", [V+"E4_Brittleness"]),
    ("tmpl:e1", "E1", "conditional classification", [V+"E1_StatusPartition", V+"E1_Internalization", V+"E1_NoGeneratorDichotomy"]),
    ("tmpl:e3", "E3", "conditional classification", [V+"E3_TwoLevelFixedPoint", V+"E3_StatusPartition", V+"E3_RegressStoppedByE2", V+"E3_AblationSeparation"]),
    ("tmpl:e4", "E4", "certificate specification", [V+"compilationLawful_requiredCoreGatesPass", V+"E4_Compilation", V+"E4_StatusPartition"]),
    ("def:e5", "E5", "definition", [V+"CompleteCollapseRescueInventory", V+"CollapsedCore"]),
    ("lem:e5", "E5", "consistency lemma", [V+"E5_CollapseFalsifier", V+"E5_ReclosureCollapse", V+"E5_RevivedExcludesLowerPriority", V+"E5_IrreversibleCollapse", V+"E5_SubsidyWithdrawalReclassification"]),
    ("tmpl:e7", "E7", "conditional classification", [V+"E7_AlarmTrichotomy", V+"E7_PreemptionSignature"]),
    ("def:e8", "E8", "definition", [V+"ControlPriceComponent"]),
    ("lem:e8", "E8, E8.1", "consistency lemma", [V+"E8_ControlPrice", V+"E8_ComponentShadowPrice", V+"E8_CompressedSummaryLawfulness", V+"E8_1_AuditCapture", V+"E8_1_CaptureFalsifier", V+"E8_1_MetaAuditBoundedByE2", V+"BudgetInflationAudit.lineageMustMatchClassifiedMove"]),
    ("tmpl:e10", "E10--E10.2", "conditional classification", [V+"E10_CognitiveDemarcation", V+"E10_ScheduleTrapNull", V+"E10_ScheduleTrapExcludesLowerPriority", V+"E10_DecodableCorrelate", V+"E10_1_Intention", V+"E10_1_PostHocIntentionFalsifier", V+"E10_1_PostHocIntentionExcludesLowerPriority", V+"E10_2_Goal", V+"E10_2_RewardProxyNotGoal", V+"E10_2_RewardProxyOnlyExcludesLowerPriority"]),
    ("tmpl:e11", "E11", "conditional classification", [V+"E11_StackActivity", V+"E11_Constitutive", V+"E11_ConditioningOnly", V+"E11_WashoutInert", V+"E11_NCTDObstruction", V+"E11_StatusPartition"]),
    ("tmpl:e12", "E12", "template", [V+"E12_Individuation", V+"E12_StatusPartition"]),
    ("prop:e12-singleton", "E12", "template, singleton case", [I+"singletonCandidates", I+"E12_singleton_maximal_from_tests", I+"spikeSelfMaintained"]),
    ("tmpl:e13", "E13--E13.4", "template", [V+"E13_Communication", V+"E13_TeachingCapacity", V+"E13_CoercionNull", V+"E13_SymbolicRepair", V+"E13_StatusPartition", V+"E13_CoercionNullExcludesLowerPriority", I+"transportContextZero", I+"transportContextOne", I+"E13_two_contexts_distinct", I+"E13_two_contexts_members"]),
    ("tmpl:e14", "E14", "conditional classification", [V+"E14_ReconsolidationStatus", V+"E14_LawfulConflictTrichotomy", V+"E14_OutcomeCollisionExcludesLawful", V+"E14_RecordRepair", V+"E14_RecordCoarsening", V+"E14_StatusedUnresolvedChargedToLambda", V+"E14_SilentRewriteFalsifier", V+"E14_RetrievalWithoutTransportControl", V+"E14_LaunderedProvenanceDefect"]),
    ("tmpl:e15", "E15", "conditional classification", [V+"E15_OfflineReclosureStatus", V+"E15_DeficitAlternation", V+"E15_OnlineSufficientNoOfflineRequired", V+"E15_OfflinePermittedOutsideDeficit", V+"E15_SkippedOfflineCascade", V+"E15_DecorativeOfflineFalsifier", V+"E15_DutyCycleMismatchFalsifier", V+"E15_DeficitOnlineFalsifiesNecessity", V+"E15_DeficitCounterexampleExcludesLowerPriority", V+"E15_OffInventoryFlowCannotCertifyOffline"]),
    ("tmpl:e16", "E16", "conditional classification", [V+"E16_AdaptabilityStatus", V+"E16_CoherentAdaptability", V+"E16_CurrentAuditBlindness", V+"E16_RouteManufacturesRepairCapacity", V+"E16_ArtifactNotAdaptability", V+"E16_FlatNoAdaptability", V+"E16_FlattenableNotAdaptability", V+"E16_CurrentizableIsLegibleSlack", V+"E16_DissipativeNotAdaptability", V+"E16_BoundedPerturbationFailureRejected", V+"E16_SupportConfoundExcludesLowerPriority", V+"E16_LoopAsymmetryAnchor", V+"E16_SwappedRouteTrialPopulationRejected", V+"E16_FlatSecondArmUsesClaimLinkedPair", V+"E16_UnrelatedEqualPairCannotReplaceClaimDifference"]),
]


def short(fq):
    return fq.replace("SixBirdsFoundationsV.", "")


missing = [d for _, _, _, ds in ITEMS for d in ds if d not in DECLS]
if missing:
    sys.exit("missing declarations: " + ", ".join(missing))

rows = []
for label, entry, role, decls in ITEMS:
    cat = f"{entry}, {role}"
    first = entry.split(",")[0].split("--")[0]
    if first in CAT:
        cat += f" \\newline catalog line {CAT[first]['line']}"
    if decls:
        cells = []
        for d in decls:
            kind, p, line = DECLS[d]
            cells.append(f"\\path{{{short(d)}}} ({kind}) \\newline \\path{{{p}}}:{line}")
        lean = " \\newline ".join(cells)
    else:
        lean = "argued on paper; not formalized"
    rows.append(f"\\Cref{{{label}}} & {cat} & {lean} \\\\")
(OUT / "concordance_rows.tex").write_text("\n".join(rows) + "\n")

# ---- Catalog index: entry, catalog name and line, paper status
PAPER = {
    "D1": "definition; general theorem", "D2": "definition; conditional general theorem",
    "D3": "definition; consistency lemma", "D4": "definition; consistency lemma",
    "D5": "definition; consistency lemma", "D6": "definition; consistency lemma",
    "E1": "law, weak instance", "E2": "law, weak instance", "E3": "law, weak instance",
    "E4": "certificate specification", "E5": "definition", "E6": "general theorem",
    "E7": "conditional classification", "E8": "definition", "E9": "general theorem",
    "E10": "conditional classification", "E11": "conditional classification", "E12": "law, weak instance",
    "E13": "law, weak instance", "E14": "conditional classification", "E15": "conditional classification",
    "E16": "conditional classification",
}
idx = []
for ent in sorted(PAPER, key=lambda g: (g[0], int(g[1:]))):
    c = CAT[ent]
    idx.append(f"{ent} & {tex(c['name'])} & {PAPER[ent]} & {c['line']} \\\\")
(OUT / "catalog_rows.tex").write_text("\n".join(idx) + "\n")

# ---- Axioms of every theorem in the concordance ------------------------------
ax = []
seen = set()
for _, _, _, decls in ITEMS:
    for d in decls:
        if d in seen or DECLS[d][0] not in ("theorem", "lemma"):
            continue
        seen.add(d)
        if d not in AX:
            sys.exit("no axiom record for " + d)
        ax.append(f"\\path{{{short(d)}}} & {tex(AX[d])} & {SRC[d]} \\\\")
(OUT / "axiom_rows.tex").write_text("\n".join(ax) + "\n")

print(f"{len(rows)} concordance rows, {len(idx)} catalog rows, {len(ax)} axiom rows")
