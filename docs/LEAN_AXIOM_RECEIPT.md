# Lean axiom receipt for the Foundations V authored theorems

Generated 2026-09-02 on a scratch copy of the frozen `lean/` tree (copied to a
temporary directory outside the repository; nothing was copied back).
Toolchain: `leanprover/lean4:v4.28.0` (from `lean/lean-toolchain`).

Original receipt procedure: `lake build` (default targets; 75 jobs, success,
three `unusedVariables` warnings in `E15OfflineReclosure.lean`), then `lake
build SixBirdsFoundationsV.Laws.E16Adaptability HolonomyMemory`, then a scratch
file importing `SixBirdsFoundationsV`,
`SixBirdsFoundationsV.Laws.E16Adaptability`, and `HolonomyMemory` and running
`#print axioms` on every declaration tagged `kind = "theorem"` in
`formalization/manifests/foundations_v_manifest.toml` (187 names).

Packaging update, 2026-09-04: the root module now imports E16. The current
default `lake build` compiles E16 and completes successfully in 76 jobs. This
changes build coverage, not the theorem bodies or the axiom footprints below.

Result: all 187 names elaborate; none depends on `sorryAx` or on any non-core axiom. Footprint census: 98 axiom-free; 12 `propext` only; 12 `propext, Quot.sound`; 1 `Quot.sound` only; 64 `propext, Classical.choice, Quot.sound`.

A separate pattern scan of the authored tree (`lean/SixBirdsFoundationsV/`) for `sorry`, `axiom`, `admit`, `opaque`, `unsafe`, `native_decide` found no such declarations or tactics (the word `opaque` occurs only inside comments at `Definitional/CarriedRecord.lean:85` and `Laws/E1Internalization.lean:89`); the same scan of `lean/vendor/` found none.

| Declaration | Axioms |
|---|---|
| `SixBirdsFoundationsV.join_refines_left` | none |
| `SixBirdsFoundationsV.join_refines_right` | none |
| `SixBirdsFoundationsV.vee_greatest_lower_bound` | none |
| `SixBirdsFoundationsV.join_well_defined` | none |
| `SixBirdsFoundationsV.join_idem` | none |
| `SixBirdsFoundationsV.join_comm` | none |
| `SixBirdsFoundationsV.join_assoc` | none |
| `SixBirdsFoundationsV.predictiveSurplus_identical` | none |
| `SixBirdsFoundationsV.predictiveSurplus_profile_identical` | none |
| `SixBirdsFoundationsV.predictiveSurplus_exact_baseline` | none |
| `SixBirdsFoundationsV.predictiveSurplusValue_nonnegative_iff` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.predictiveSurplusValue_identical` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.predictiveSurplusValue_exact_baseline` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.predictiveSurplusXi_nonnegative_of_psd` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.predictiveSurplusXi_chain_rule_monotone` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.predictiveSurplusXi_same_family_saturation` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.carriedSource_committed_state` | none |
| `SixBirdsFoundationsV.carriedSource_audited_cell_records` | none |
| `SixBirdsFoundationsV.carriedSource_allowed_tag` | none |
| `SixBirdsFoundationsV.not_carriedSource_fallback` | none |
| `SixBirdsFoundationsV.not_carriedSource_independent_pair_witness` | none |
| `SixBirdsFoundationsV.not_carriedSource_simulation_trace` | none |
| `SixBirdsFoundationsV.not_carriedSource_ablation_record` | none |
| `SixBirdsFoundationsV.not_carriedSource_unknown` | none |
| `SixBirdsFoundationsV.not_carriedSource_contradictory` | none |
| `SixBirdsFoundationsV.ownKernelTraceTo_step_in_scope` | none |
| `SixBirdsFoundationsV.ownKernelTraceTo_suppK` | none |
| `SixBirdsFoundationsV.not_ownKernelTraceTo_of_step_not_in_scope` | none |
| `SixBirdsFoundationsV.not_carriedRecord_of_step_not_in_scope` | none |
| `SixBirdsFoundationsV.not_carriedInstrument_of_incomplete_inventory` | none |
| `SixBirdsFoundationsV.not_carriedInstrument_empty_without_complete_inventory` | none |
| `SixBirdsFoundationsV.repairSort_ne_p6` | none |
| `SixBirdsFoundationsV.no_repairSort_p6` | none |
| `SixBirdsFoundationsV.carriedLedger_has_complete_inventory` | none |
| `SixBirdsFoundationsV.no_carriedLedger_with_false_inventory` | none |
| `SixBirdsFoundationsV.carriedRecordEvidence_uses_policy` | none |
| `SixBirdsFoundationsV.hasCarriedRecordEvidence_uses_policy` | none |
| `SixBirdsFoundationsV.not_hasCarriedRecordEvidence_without_policy_witness` | none |
| `SixBirdsFoundationsV.carriedLedger_entry_uses_policy` | none |
| `SixBirdsFoundationsV.repairMove_record_uses_policy` | none |
| `SixBirdsFoundationsV.activeCarriedInstrument_has_carried_instrument` | none |
| `SixBirdsFoundationsV.lawfulRepairStep_requires_detection` | none |
| `SixBirdsFoundationsV.lawfulRepairStep_requires_gate` | none |
| `SixBirdsFoundationsV.lawfulRepairStep_requires_kernel_transition` | none |
| `SixBirdsFoundationsV.lawfulRepairStep_requires_reaudit` | none |
| `SixBirdsFoundationsV.not_lawfulRepairStep_without_detection` | none |
| `SixBirdsFoundationsV.not_lawfulRepairStep_without_gate` | none |
| `SixBirdsFoundationsV.not_lawfulRepairStep_without_kernel_transition` | none |
| `SixBirdsFoundationsV.not_lawfulRepairStep_without_reaudit` | none |
| `SixBirdsFoundationsV.closedLoopScope_complete` | none |
| `SixBirdsFoundationsV.closedLoopScope_entry_carried` | none |
| `SixBirdsFoundationsV.carriedRecordAt_carriedSource` | none |
| `SixBirdsFoundationsV.not_carriedRecordAt_of_source_fallback` | none |
| `SixBirdsFoundationsV.not_carriedRecordAt_of_source_unknown` | none |
| `SixBirdsFoundationsV.not_carriedRecordAt_of_source_contradictory` | none |
| `SixBirdsFoundationsV.not_carriedRecordAt_of_generatedByS_false` | none |
| `SixBirdsFoundationsV.not_carriedRecordAt_of_inScope_false` | none |
| `SixBirdsFoundationsV.not_repairTypedAuditEntryCarried_of_source_fallback` | none |
| `SixBirdsFoundationsV.not_repairTypedAuditEntryCarried_of_source_unknown` | none |
| `SixBirdsFoundationsV.not_repairTypedAuditEntryCarried_of_source_contradictory` | none |
| `SixBirdsFoundationsV.not_repairTypedAuditEntryCarried_of_source_independent_pair_witness` | none |
| `SixBirdsFoundationsV.not_repairTypedAuditEntryCarried_of_source_simulation_trace` | none |
| `SixBirdsFoundationsV.not_repairTypedAuditEntryCarried_of_source_ablation_record` | none |
| `SixBirdsFoundationsV.not_repairTypedAuditEntryCarried_of_generatedByS_false` | none |
| `SixBirdsFoundationsV.not_repairTypedAuditEntryCarried_of_inScope_false` | none |
| `SixBirdsFoundationsV.not_closedLoopScope_of_listed_source_fallback` | none |
| `SixBirdsFoundationsV.not_closedLoopScope_of_listed_source_unknown` | none |
| `SixBirdsFoundationsV.not_closedLoopScope_of_listed_source_contradictory` | none |
| `SixBirdsFoundationsV.not_closedLoopScope_of_listed_generatedByS_false` | none |
| `SixBirdsFoundationsV.not_closedLoopScope_of_listed_inScope_false` | none |
| `SixBirdsFoundationsV.fallback_entry_cannot_borrow_carriedness` | none |
| `SixBirdsFoundationsV.lawfulAcquisition_requires_acquisitionStrict` | none |
| `SixBirdsFoundationsV.not_lawfulAcquisition_of_sameFamilySaturated` | none |
| `SixBirdsFoundationsV.lawfulAllocation_support_eq` | none |
| `SixBirdsFoundationsV.lawfulAllocation_no_new_active_probe` | none |
| `SixBirdsFoundationsV.lawfulRetirement_requires_active` | none |
| `SixBirdsFoundationsV.lawfulRetirement_probe_absent_after` | none |
| `SixBirdsFoundationsV.xi_sameFamilySaturated_of_sameFamilySaturation` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.xi_sameFamilySaturated_not_acquisitionStrict` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E6_AttentionKKT` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E6_SlackCollapse` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E9_SameFamilyStrictness` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.exists_max_ratio` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E9_CuriosityArgmax` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E6_E9_AccessArbitration` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E6_E9_AccessArbitration_epsilon` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.selected_access_move_ratio_bound` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.selected_access_move_ratio_bound_epsilon` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E7_AlarmTrichotomy` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E7_PreemptionSignature` | none |
| `SixBirdsFoundationsV.E1_StatusPartition` | none |
| `SixBirdsFoundationsV.E1_Internalization` | none |
| `SixBirdsFoundationsV.E1_StrictSelfExtension` | none |
| `SixBirdsFoundationsV.E1_NoGeneratorDichotomy` | none |
| `SixBirdsFoundationsV.E2_SelfSoundnessObstruction` | propext |
| `SixBirdsFoundationsV.E2_ForcedStratification` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.list_length_le_of_nodup_subset` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.TowerSlotFootprint_eq_records_length` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.mem_TowerRecordListForSlots` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.TowerRecordListForSlots_subset_carrier` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.TowerRecordListForSlots_nodup` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.foldl_add_eq_init_add_ListNatSumBy` | propext, Quot.sound |
| `SixBirdsFoundationsV.foldl_add_zero_eq_ListNatSumBy` | propext, Quot.sound |
| `SixBirdsFoundationsV.TowerRecordListForSlots_length_eq_footprint` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.TowerFootprint_eq_slotFootprint_foldl` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.TowerFootprint_eq_TowerFootprintForSlots_range` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E2_CapacityBound` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E2_StatusPartition` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E3_TwoLevelFixedPoint` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E3_StatusPartition` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E3_RegressStoppedByE2` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E3_AblationSeparation` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E11_StackActivity` | none |
| `SixBirdsFoundationsV.E11_Constitutive` | none |
| `SixBirdsFoundationsV.E11_ConditioningOnly` | none |
| `SixBirdsFoundationsV.E11_WashoutInert` | none |
| `SixBirdsFoundationsV.E11_NCTDObstruction` | propext |
| `SixBirdsFoundationsV.E11_StatusPartition` | none |
| `SixBirdsFoundationsV.E12_Individuation` | none |
| `SixBirdsFoundationsV.E12_StatusPartition` | none |
| `SixBirdsFoundationsV.compilationLawful_requiredCoreGatesPass` | propext |
| `SixBirdsFoundationsV.E4_Compilation` | propext, Quot.sound |
| `SixBirdsFoundationsV.E4_Brittleness` | none |
| `SixBirdsFoundationsV.E4_StatusPartition` | propext |
| `SixBirdsFoundationsV.E5_CollapseFalsifier` | none |
| `SixBirdsFoundationsV.E5_ReclosureCollapse` | none |
| `SixBirdsFoundationsV.E5_IrreversibleCollapse` | none |
| `SixBirdsFoundationsV.E5_SubsidyWithdrawalReclassification` | none |
| `SixBirdsFoundationsV.BudgetInflationAudit.lineageMustMatchClassifiedMove` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E8_ControlPrice` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E8_ComponentShadowPrice` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E8_CompressedSummaryLawfulness` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E8_1_AuditCapture` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E8_1_CaptureFalsifier` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E8_1_MetaAuditBoundedByE2` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E13_Communication` | none |
| `SixBirdsFoundationsV.E13_TeachingCapacity` | none |
| `SixBirdsFoundationsV.E13_CoercionNull` | none |
| `SixBirdsFoundationsV.E13_SymbolicRepair` | none |
| `SixBirdsFoundationsV.E13_StatusPartition` | propext |
| `SixBirdsFoundationsV.E10_CognitiveDemarcation` | propext |
| `SixBirdsFoundationsV.E10_DecodableCorrelate` | none |
| `SixBirdsFoundationsV.E10_ScheduleTrapNull` | none |
| `SixBirdsFoundationsV.E10_1_Intention` | propext |
| `SixBirdsFoundationsV.E10_1_PostHocIntentionFalsifier` | none |
| `SixBirdsFoundationsV.E10_2_Goal` | propext |
| `SixBirdsFoundationsV.E10_2_RewardProxyNotGoal` | none |
| `SixBirdsFoundationsV.E5_RevivedExcludesLowerPriority` | none |
| `SixBirdsFoundationsV.E10_ScheduleTrapExcludesLowerPriority` | propext |
| `SixBirdsFoundationsV.E10_1_PostHocIntentionExcludesLowerPriority` | propext |
| `SixBirdsFoundationsV.E10_2_RewardProxyOnlyExcludesLowerPriority` | propext |
| `SixBirdsFoundationsV.E13_CoercionNullExcludesLowerPriority` | propext |
| `SixBirdsFoundationsV.E14_ReconsolidationStatus` | propext, Quot.sound |
| `SixBirdsFoundationsV.E14_LawfulConflictTrichotomy` | propext, Quot.sound |
| `SixBirdsFoundationsV.E14_OutcomeCollisionExcludesLawful` | propext, Quot.sound |
| `SixBirdsFoundationsV.E14_RecordRepair` | propext, Quot.sound |
| `SixBirdsFoundationsV.E14_RecordCoarsening` | propext, Quot.sound |
| `SixBirdsFoundationsV.E14_StatusedUnresolvedChargedToLambda` | propext, Quot.sound |
| `SixBirdsFoundationsV.E14_SilentRewriteFalsifier` | propext, Quot.sound |
| `SixBirdsFoundationsV.E14_RetrievalWithoutTransportControl` | propext, Quot.sound |
| `SixBirdsFoundationsV.E14_LaunderedProvenanceDefect` | none |
| `SixBirdsFoundationsV.E15_OfflineReclosureStatus` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E15_DeficitAlternation` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E15_OfflineCapacityExactlyFreed` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E15_OnlineSufficientNoOfflineRequired` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E15_OfflinePermittedOutsideDeficit` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E15_SkippedOfflineCascade` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E15_DecorativeOfflineFalsifier` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E15_DutyCycleMismatchFalsifier` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E15_DeficitOnlineFalsifiesNecessity` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E15_DeficitCounterexampleExcludesLowerPriority` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E15_OffInventoryFlowCannotCertifyOffline` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E16_SwappedRouteTrialPopulationRejected` | propext, Quot.sound |
| `SixBirdsFoundationsV.E16_FlatSecondArmUsesClaimLinkedPair` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E16_UnrelatedEqualPairCannotReplaceClaimDifference` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E16_AdaptabilityStatus` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E16_CoherentAdaptability` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E16_CurrentAuditBlindness` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E16_RouteManufacturesRepairCapacity` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E16_ArtifactNotAdaptability` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E16_FlatNoAdaptability` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E16_FlattenableNotAdaptability` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E16_CurrentizableIsLegibleSlack` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E16_DissipativeNotAdaptability` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E16_BoundedPerturbationFailureRejected` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E16_SupportConfoundExcludesLowerPriority` | propext, Classical.choice, Quot.sound |
| `SixBirdsFoundationsV.E16_LoopAsymmetryAnchor` | Quot.sound |
