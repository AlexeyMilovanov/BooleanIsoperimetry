import HarperStability.Assembly
import HarperStability.Assembly.EffectiveUniform

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
