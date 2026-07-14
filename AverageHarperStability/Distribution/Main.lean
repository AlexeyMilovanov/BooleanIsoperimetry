import AverageHarperStability.Distribution.Tracking

namespace AverageHarperStability

/-! Assembly of Lemmas L0--L9 and corrected Corollary 10. -/

theorem distribution_average_harper_stability : DistributionStabilityStatement := by
  intro tau zeta ht0 ht1 hz0 hz1
  use delta0_val tau zeta
  refine ⟨delta0_val_pos ht0 ht1 hz0 hz1, err_val tau zeta, ?_, ?_, ?_⟩
  · exact err_val_tendsto ht0 ht1 hz0 hz1
  · intro delta hd0 hd1
    exact err_val_pos ht0 ht1 hz0 hz1 hd0
  · intro n mu delta hn hmu hd0 hd1 u p hzeta1 hzeta2 h_ent
    exact distribution_stability_core ht0 ht1 hz0 hz1 n mu delta hn hmu hd0 hd1 hzeta1 hzeta2 h_ent

end AverageHarperStability
