import HarperStability.Assembly
import HarperStability.Assembly.EffectiveUniform
import AverageHarperStability

-- o(n) skeleton route
#print axioms HarperStability.q_from_s7_skeleton
#print axioms HarperStability.component_package_skeleton
#print axioms HarperStability.main_from_components
#print axioms HarperStability.main_finite_skeleton

-- effective (explicit envelope) and uniform (class-only K), plus the bridges
#print axioms HarperStability.main_finite_effective
#print axioms HarperStability.main_finite_via_effective
#print axioms HarperStability.main_finite_effective_uniform
#print axioms HarperStability.main_finite_effective_of_uniform

-- combinatorial average-Harper stability and its principal bridges
#print axioms AverageHarperStability.uniformMass_isLaw
#print axioms AverageHarperStability.entropy_uniformMass
#print axioms AverageHarperStability.noiseMass_isLaw
#print axioms AverageHarperStability.mglCurve_strictConvex
#print axioms AverageHarperStability.distribution_average_harper_stability
#print axioms AverageHarperStability.entropy_labels_to_cover
#print axioms AverageHarperStability.average_harper_set_stability
