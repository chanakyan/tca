-- SPDX-License-Identifier: BSD-2-Clause
import TemporalClosureAlgebra
import QuantumAsTCA
import SpacetimeAsTCA
import InformationParadox

-- TCA
#print axioms TCA.Theorem_Irreversibility_of_Closure
#print axioms TCA.Theorem_Coupling
#print axioms TCA.Theorem_Default_as_Limit
#print axioms TCA.TSF_Axiom_2_as_TCA_Theorem

-- Quantum v0.2
#print axioms QuantumAsTCA.Theorem_Unitary_Evolution_Has_No_Closures
#print axioms QuantumAsTCA.Theorem_PVM_Posts_Both_Sides
#print axioms QuantumAsTCA.Theorem_PVM_Satisfies_DoubleEntry
#print axioms QuantumAsTCA.Theorem_Measurement_Ledger_Is_Monotone
#print axioms QuantumAsTCA.Theorem_Measurement_Is_Irreversible
#print axioms QuantumAsTCA.Theorem_Entanglement_Is_Shared_Preparation_Coupling
#print axioms QuantumAsTCA.Corollary_Measurement_And_Entanglement

-- Resolved (were deferred, now fully proved)
#print axioms TCA.Theorem_Finite_Externalization
#print axioms TCA.synchronous_closure_collapse

-- Spacetime
#print axioms SpacetimeAsTCA.Theorem_Geodesic_Incompleteness_Is_Default
#print axioms SpacetimeAsTCA.Theorem_Default_Persists
#print axioms SpacetimeAsTCA.Theorem_Completed_Geodesic_Irreversible
#print axioms SpacetimeAsTCA.Theorem_Singularity_Is_Permanent_Default
#print axioms SpacetimeAsTCA.Theorem_BlackHole_Events_Are_Coupled

-- Information Paradox
#print axioms InformationParadox.IP1_monotone_time_per_substrate
#print axioms InformationParadox.IP2_spacetime_open_independent_of_quantum
#print axioms InformationParadox.IP3_spacetime_information_persists
#print axioms InformationParadox.IP4_information_never_lost
#print axioms InformationParadox.evaporation_dichotomy
