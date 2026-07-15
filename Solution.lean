import HarperStability.Assembly.Basic

/-!
# Comparator solution bridge

The theorem below has exactly the name and type used in `Challenge.lean` and
is proved solely by the project's checked headline theorem.
-/

theorem robust_harper_stability : HarperStability.MainFiniteStatement :=
  HarperStability.main_finite_skeleton
