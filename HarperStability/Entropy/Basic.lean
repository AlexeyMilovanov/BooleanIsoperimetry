import HarperStability.Interface

namespace HarperStability

/-!
Finite entropy toolkit.

This file is the first proof target for the formalization.  The statements
below are intentionally small: they are the reusable entropy facts needed by
S1--S7.  They use only finite counting over `Finset`, not `MeasureTheory`.
-/

variable {m : ℕ} {β γ : Type*} [DecidableEq β] [DecidableEq γ]

omit [DecidableEq β] in
theorem pOn_nonneg (A : Finset (Cube m)) (f : Cube m → β) (b : β) :
    0 ≤ pOn A f b := by
  unfold pOn
  positivity

omit [DecidableEq β] in
theorem pOn_le_one (A : Finset (Cube m)) (f : Cube m → β) (b : β) :
    pOn A f b ≤ 1 := by
  classical
  unfold pOn
  by_cases hA : A.card = 0
  · simp [hA]
  · have hpos_nat : 0 < A.card := Nat.pos_of_ne_zero hA
    have hpos : 0 < (A.card : ℝ) := by
      exact_mod_cast hpos_nat
    have hle_nat : (A.filter fun x => f x = b).card ≤ A.card := by
      exact Finset.card_filter_le A (fun x => f x = b)
    rw [div_le_one hpos]
    show (((A.filter fun x => f x = b).card : ℕ) : ℝ) ≤ (A.card : ℝ)
    exact_mod_cast hle_nat

omit [DecidableEq β] in
theorem uH_nonneg (A : Finset (Cube m)) (f : Cube m → β) :
    0 ≤ uH A f := by
  classical
  unfold uH
  exact Finset.sum_nonneg fun b _ =>
    Real.negMulLog_nonneg (pOn_nonneg A f b) (pOn_le_one A f b)

omit [DecidableEq β] in
lemma sum_pOn_image_eq_one (A : Finset (Cube m)) (hA : A.Nonempty)
    (f : Cube m → β) :
    (∑ b ∈ @Finset.image (Cube m) β
      (fun a b => Classical.propDecidable (a = b)) f A, pOn A f b) = 1 := by
  let img : Finset β :=
    @Finset.image (Cube m) β (fun a b => Classical.propDecidable (a = b)) f A
  have hcard_pos : 0 < (A.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hA)
  have hcard_ne : (A.card : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hmap : (A : Set (Cube m)).MapsTo f img := by
    intro x hx
    letI : DecidableEq β := Classical.decEq β
    change f x ∈ A.image f
    exact Finset.mem_image_of_mem f (by simpa using hx)
  have hsum_nat : A.card =
      ∑ b ∈ img,
        (@Finset.filter (Cube m) (fun x => f x = b)
          (fun x => Classical.propDecidable (f x = b)) A).card := by
    letI : DecidableEq β := Classical.decEq β
    simpa [img] using
      (Finset.card_eq_sum_card_fiberwise (s := A) (t := img) (f := f) hmap)
  have hsum_real :
      (∑ b ∈ img,
        ((@Finset.filter (Cube m) (fun x => f x = b)
          (fun x => Classical.propDecidable (f x = b)) A).card : ℝ)) =
        (A.card : ℝ) := by
    exact_mod_cast hsum_nat.symm
  change (∑ b ∈ img,
      ((@Finset.filter (Cube m) (fun x => f x = b)
        (fun x => Classical.propDecidable (f x = b)) A).card : ℝ) /
        (A.card : ℝ)) = 1
  rw [← Finset.sum_div]
  rw [hsum_real]
  exact div_self hcard_ne

theorem uH_le_log_card_image (A : Finset (Cube m)) (hA : A.Nonempty)
    (f : Cube m → β) :
    uH A f ≤ Real.log ((A.image f).card : ℝ) := by
  classical
  let img : Finset β :=
    @Finset.image (Cube m) β (fun a b => Classical.propDecidable (a = b)) f A
  let n : ℝ := (img.card : ℝ)
  have himage_nonempty : img.Nonempty := by
    rcases hA with ⟨x, hx⟩
    letI : DecidableEq β := Classical.decEq β
    exact ⟨f x, by
      change f x ∈ A.image f
      exact Finset.mem_image_of_mem f hx⟩
  have hn_pos : 0 < n := by
    dsimp [n]
    exact_mod_cast (Finset.card_pos.mpr himage_nonempty)
  have hn_ne : n ≠ 0 := ne_of_gt hn_pos
  have hweights :
      ∑ b ∈ img, (n⁻¹ : ℝ) = 1 := by
    simp [n, hn_ne]
  have hmean :
      (∑ b ∈ img, n⁻¹ • pOn A f b) = n⁻¹ := by
    rw [← Finset.smul_sum]
    rw [sum_pOn_image_eq_one A hA f]
    simp
  have hjensen :
      (∑ b ∈ img, n⁻¹ • Real.negMulLog (pOn A f b)) ≤
        Real.negMulLog (∑ b ∈ img, n⁻¹ • pOn A f b) := by
    exact Real.concaveOn_negMulLog.le_map_sum
      (fun _ _ => inv_nonneg.mpr (le_of_lt hn_pos))
      hweights
      (fun b hb => pOn_nonneg A f b)
  have hmul := mul_le_mul_of_nonneg_left hjensen (le_of_lt hn_pos)
  have hleft :
      n * (∑ b ∈ img, n⁻¹ • Real.negMulLog (pOn A f b)) =
        uH A f := by
    unfold uH
    change n * (∑ b ∈ img, n⁻¹ • Real.negMulLog (pOn A f b)) =
      ∑ b ∈ img, Real.negMulLog (pOn A f b)
    simp only [smul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr (rfl : img = img) ?_
    intro b hb
    rw [← mul_assoc, mul_inv_cancel₀ hn_ne, one_mul]
  have hcard_image : img.card = (A.image f).card := by
    have himg : img = A.image f := by
      ext b
      simp [img]
    rw [himg]
  have hright :
      n * Real.negMulLog (∑ b ∈ img, n⁻¹ • pOn A f b) =
        Real.log ((A.image f).card : ℝ) := by
    rw [hmean]
    unfold Real.negMulLog n
    rw [Real.log_inv]
    calc
      (img.card : ℝ) * (-(img.card : ℝ)⁻¹ * -Real.log (img.card : ℝ))
          = (img.card : ℝ) *
              ((img.card : ℝ)⁻¹ * Real.log (img.card : ℝ)) := by ring
      _ = ((img.card : ℝ) * (img.card : ℝ)⁻¹) *
              Real.log (img.card : ℝ) := by rw [mul_assoc]
      _ = 1 * Real.log (img.card : ℝ) := by
            rw [mul_inv_cancel₀]
            exact_mod_cast (ne_of_gt (Finset.card_pos.mpr himage_nonempty))
      _ = Real.log ((A.image f).card : ℝ) := by
            rw [one_mul, hcard_image]
  rw [hleft, hright] at hmul
  exact hmul

lemma pOn_eq_one_div_card {m : ℕ} {B : Type*}
    (A : Finset (Cube m)) (f : Cube m → B) (x : Cube m) (hx : x ∈ A)
    (h_inj : ∀ y ∈ A, f y = f x → y = x) :
    pOn A f (f x) = 1 / (A.card : ℝ) := by
  unfold pOn
  congr 1
  have h_filter : @Finset.filter (Cube m) (fun x_1 => f x_1 = f x) (fun x_1 => Classical.propDecidable (f x_1 = f x)) A = {x} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hyA, hyp⟩
      exact h_inj y hyA hyp
    · intro hy
      subst hy
      exact ⟨hx, rfl⟩
  have h_card : (@Finset.filter (Cube m) (fun x_1 => f x_1 = f x) (fun x_1 => Classical.propDecidable (f x_1 = f x)) A).card = 1 := by
    rw [h_filter, Finset.card_singleton]
  exact_mod_cast h_card

theorem uH_proj_univ (A : Finset (Cube m)) (hA : A.Nonempty) :
    uH A (proj (Finset.univ : Finset (Fin m))) = Real.log (A.card : ℝ) := by
  have h_proj : ∀ x : Cube m, proj (Finset.univ : Finset (Fin m)) x = x := by
    intro x
    unfold proj
    simp only [Finset.inter_univ]
  have hp : ∀ x ∈ A, pOn A (proj (Finset.univ : Finset (Fin m))) x = 1 / (A.card : ℝ) := by
    intro x hx
    have h_eq : proj (Finset.univ : Finset (Fin m)) x = x := h_proj x
    rw [← h_eq]
    apply pOn_eq_one_div_card A (proj (Finset.univ : Finset (Fin m))) x hx
    intro y _ hyx
    rw [h_proj y, h_proj x] at hyx
    exact hyx
  have himage : @Finset.image (Cube m) (Cube m) (fun a b => Classical.propDecidable (a = b)) (proj (Finset.univ : Finset (Fin m))) A = A := by
    ext y
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, hxy⟩
      rw [h_proj x] at hxy
      subst hxy
      exact hx
    · intro hy
      use y
      exact ⟨hy, h_proj y⟩
  have hsum : uH A (proj (Finset.univ : Finset (Fin m))) = ∑ b ∈ A, Real.negMulLog (1 / (A.card : ℝ)) := by
    unfold uH
    rw [himage]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hp x hx]
  rw [hsum]
  have h_card_pos : 0 < A.card := Finset.card_pos.mpr hA
  have h_card_ne_zero : (A.card : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt h_card_pos
  simp only [Finset.sum_const, nsmul_eq_mul]
  unfold Real.negMulLog
  rw [one_div, Real.log_inv]
  calc
    (A.card : ℝ) * (- (A.card : ℝ)⁻¹ * -Real.log ↑A.card) = (A.card : ℝ) * ((A.card : ℝ)⁻¹ * Real.log ↑A.card) := by ring
    _ = ((A.card : ℝ) * (A.card : ℝ)⁻¹) * Real.log ↑A.card := by rw [mul_assoc]
    _ = 1 * Real.log ↑A.card := by rw [mul_inv_cancel₀ h_card_ne_zero]
    _ = Real.log ↑A.card := by rw [one_mul]

theorem rho_nonneg (A : Finset (Cube m)) (t : Fin m) (w : Cube m) :
    0 ≤ rho A t w := by
  unfold rho
  exact pOn_nonneg _ _ _

theorem rho_le_one (A : Finset (Cube m)) (t : Fin m) (w : Cube m) :
    rho A t w ≤ 1 := by
  unfold rho
  exact pOn_le_one _ _ _

/-
Chain rule for a Boolean coordinate: the conditional entropy `H(f | g)`
for a `Bool`-valued `f` equals the `g`-fiber-averaged binary entropy of the
conditional probability `Pr[f = true | g = g x]`.
-/
set_option maxHeartbeats 1000000 in
theorem uCondH_bool_eq_uE_binEntropy {C : Type*} [DecidableEq C]
    (A : Finset (Cube m)) (hA : A.Nonempty) (f : Cube m → Bool) (g : Cube m → C) :
    uCondH A f g =
      uE A (fun x => H (pOn (A.filter fun y => g y = g x) f true)) := by
  unfold uCondH uE H pOn;
  unfold uH;
  simp +decide [ Finset.sum_div _ _ _, pOn ];
  have h_split : ∑ x ∈ Finset.image (fun x => (f x, g x)) A, Real.negMulLog ((Finset.card (Finset.filter (fun y => (f y, g y) = x) A) : ℝ) / A.card) = ∑ c ∈ Finset.image g A, ∑ b : Bool, Real.negMulLog ((Finset.card (Finset.filter (fun y => f y = b ∧ g y = c) A) : ℝ) / A.card) := by
    rw [ Finset.sum_subset ( show Finset.image ( fun x => ( f x, g x ) ) A ⊆ Finset.image ( fun x => ( x.1, x.2 ) ) ( Finset.image f A ×ˢ Finset.image g A ) from ?_ ) ];
    · rw [ Finset.sum_image ] <;> simp +decide [ Finset.sum_product ];
      rw [ Finset.sum_comm, Finset.sum_congr rfl ];
      intro x hx; rw [ Finset.sum_subset ( show Finset.image f A ⊆ { true, false } from Finset.image_subset_iff.mpr fun y hy => by cases f y <;> simp +decide ) ] <;> simp +decide ;
      constructor <;> intro h <;> simp_all +decide ; all_goals rw [ Finset.card_eq_zero.mpr ] <;> aesop;
    · intro x hx hx'; rw [ Finset.card_eq_zero.mpr ] <;> aesop;
    · simp +decide [ Finset.image_subset_iff ];
      exact fun x hx => ⟨ ⟨ x, hx, rfl ⟩, ⟨ x, hx, rfl ⟩ ⟩;
  have h_split : ∀ c ∈ Finset.image g A, ∑ b : Bool, Real.negMulLog ((Finset.card (Finset.filter (fun y => f y = b ∧ g y = c) A) : ℝ) / A.card) - Real.negMulLog ((Finset.card (Finset.filter (fun y => g y = c) A) : ℝ) / A.card) = (Finset.card (Finset.filter (fun y => g y = c) A) : ℝ) / A.card * Real.binEntropy ((Finset.card (Finset.filter (fun y => f y = true ∧ g y = c) A) : ℝ) / (Finset.card (Finset.filter (fun y => g y = c) A) : ℝ)) := by
    intro c hc
    have h_card : Finset.card (Finset.filter (fun y => g y = c) A) = Finset.card (Finset.filter (fun y => f y = true ∧ g y = c) A) + Finset.card (Finset.filter (fun y => f y = false ∧ g y = c) A) := by
      rw [ ← Finset.card_union_of_disjoint ];
      · congr with x ; by_cases hx : f x <;> aesop;
      · exact Finset.disjoint_filter.mpr ( by aesop );
    by_cases h : Finset.card ( Finset.filter ( fun y => f y = true ∧ g y = c ) A ) = 0 <;> by_cases h' : Finset.card ( Finset.filter ( fun y => f y = false ∧ g y = c ) A ) = 0 <;> simp_all +decide [ Real.binEntropy ];
    · grind +qlia;
    · rw [ show ( Finset.filter ( fun y => f y = true ∧ g y = c ) A ) = ∅ by ext x; aesop ] ; norm_num;
    · rw [ Finset.card_eq_zero.mpr ] <;> aesop;
    · unfold Real.negMulLog;
      rw [ one_sub_div ];
      · rw [ Real.log_div, Real.log_div, Real.log_div ] <;> norm_num;
        any_goals tauto;
        · rw [ Real.log_div, Real.log_div ] <;> norm_num;
          · field_simp;
            rw [ eq_div_iff ] <;> ring_nf;
            exact ne_of_gt ( add_pos_of_pos_of_nonneg ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ⟨ h.choose, Finset.mem_filter.mpr ⟨ h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2 ⟩ ⟩ ) ) ( Nat.cast_nonneg _ ) );
          · exact h';
          · exact ne_of_gt ( add_pos_of_pos_of_nonneg ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ⟨ h.choose, Finset.mem_filter.mpr ⟨ h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2 ⟩ ⟩ ) ) ( Nat.cast_nonneg _ ) );
          · exact ne_of_gt ( add_pos_of_pos_of_nonneg ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ⟨ h.choose, Finset.mem_filter.mpr ⟨ h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2 ⟩ ⟩ ) ) ( Nat.cast_nonneg _ ) );
          · exact h;
        · exact ne_of_gt ( add_pos_of_pos_of_nonneg ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ⟨ h.choose, Finset.mem_filter.mpr ⟨ h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2 ⟩ ⟩ ) ) ( Nat.cast_nonneg _ ) );
        · exact Finset.Nonempty.ne_empty hA;
        · exact Finset.Nonempty.ne_empty hA;
        · exact Finset.Nonempty.ne_empty hA;
      · exact ne_of_gt ( add_pos_of_pos_of_nonneg ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ⟨ h.choose, Finset.mem_filter.mpr ⟨ h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2 ⟩ ⟩ ) ) ( Nat.cast_nonneg _ ) );
  convert Finset.sum_congr rfl h_split using 1;
  · simp +decide only [Finset.sum_sub_distrib];
    congr! 1;
    · grind;
    · convert rfl;
  · rw [ Finset.sum_image' ];
    simp +decide [ div_eq_inv_mul, Finset.filter_filter ];
    intro x hx; rw [ Finset.sum_congr rfl fun y hy => by rw [ show g y = g x from by aesop ] ] ; simp +decide [ mul_assoc, mul_left_comm ] ;
    exact Or.inl <| Or.inl <| by congr; ext; aesop;

theorem hstep_eq_uE_binEntropy_rho (A : Finset (Cube m)) (hA : A.Nonempty)
    (t : Fin m) :
    hstep A t =
      uE A (fun x =>
        H (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x))) := by
  unfold hstep
  rw [uCondH_bool_eq_uE_binEntropy A hA (coord t)
    (proj (below (Finset.univ : Finset (Fin m)) t))]
  rfl

theorem hstep_nonneg (A : Finset (Cube m)) (hA : A.Nonempty) (t : Fin m) :
    0 ≤ hstep A t := by
  rw [hstep_eq_uE_binEntropy_rho A hA t]
  unfold uE
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro x _
    exact Real.binEntropy_nonneg (rho_nonneg A t _) (rho_le_one A t _)
  · exact Nat.cast_nonneg _

theorem hstep_le_log_two (A : Finset (Cube m)) (hA : A.Nonempty) (t : Fin m) :
    hstep A t ≤ Real.log 2 := by
  rw [hstep_eq_uE_binEntropy_rho A hA t]
  unfold uE
  have hcard_pos : (0 : ℝ) < (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hA
  rw [div_le_iff₀ hcard_pos]
  calc
    (∑ x ∈ A, H (rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x)))
        ≤ ∑ _x ∈ A, Real.log 2 := by
          apply Finset.sum_le_sum
          intro x _
          exact Real.binEntropy_le_log_two
    _ = Real.log 2 * (A.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem uH_proj_chain (A : Finset (Cube m)) (hA : A.Nonempty)
    (I : Finset (Fin m)) :
    uH A (proj I) =
      ∑ t ∈ I, uCondH A (coord t) (proj (below I t)) := by
  induction' I using Finset.strongInduction with I ih generalizing A;
  by_cases hI : I.Nonempty;
  · -- Let $t^* = \max(I)$.
    obtain ⟨t_star, ht_star⟩ : ∃ t_star ∈ I, ∀ t ∈ I, t ≤ t_star := by
      exact ⟨ Finset.max' I hI, Finset.max'_mem _ _, fun t ht => Finset.le_max' _ _ ht ⟩;
    -- By definition of $uH$, we can write
    have h_uH_def : uH A (proj I) = uH A (fun x => (coord t_star x, proj (I.erase t_star) x)) := by
      have h_uH_def : ∀ x y : Cube m, proj I x = proj I y ↔ (coord t_star x = coord t_star y ∧ proj (I.erase t_star) x = proj (I.erase t_star) y) := by
        intro x y; constructor <;> intro h <;> simp_all +decide [ Finset.ext_iff, proj ] ;
        · unfold coord; specialize h t_star ht_star.1; aesop;
        · intro a ha; by_cases ha' : a = t_star <;> simp_all +decide [ coord ] ;
      refine' Finset.sum_bij ( fun x hx => ( x.filter ( fun t => t = t_star ) |> Finset.card |> fun n => decide ( n = 1 ), x.filter ( fun t => t ∈ I.erase t_star ) ) ) _ _ _ _ <;> simp +decide [ * ];
      · intro x hx; use x; simp +decide [ Finset.filter_eq', Finset.filter_and, * ] ;
        unfold coord proj; aesop;
      · intro x hx y hy h₁ h₂; specialize h_uH_def x y; simp_all +decide [ Finset.filter_eq', Finset.filter_and ] ;
        unfold coord proj at *; simp_all +decide [ Finset.ext_iff ] ;
        grind;
      · intro x hx; use x; simp +decide [ Finset.filter_eq', Finset.filter_and ] ;
        unfold proj coord; aesop;
      · intro x hx; unfold pOn; simp +decide [ Finset.filter_eq', Finset.filter_and, * ] ;
        congr! 3;
        congr! 2;
        · unfold coord proj; aesop;
        · ext; simp +decide [ Finset.ext_iff, proj ] ;
          grind;
    -- By definition of $uCondH$, we can write
    have h_uCondH_def : uH A (fun x => (coord t_star x, proj (I.erase t_star) x)) = uCondH A (coord t_star) (proj (I.erase t_star)) + uH A (proj (I.erase t_star)) := by
      unfold uCondH; ring;
    rw [ h_uH_def, h_uCondH_def, ih ( I.erase t_star ) ( Finset.erase_ssubset ht_star.1 ) A hA ];
    rw [ ← Finset.sum_erase_add _ _ ht_star.1, add_comm ];
    congr! 2;
    · congr! 2;
      ext; simp [below];
      grind;
    · ext; simp [proj, below];
      exact fun _ => ⟨ fun h => ⟨ h.2, lt_of_le_of_ne ( ht_star.2 _ h.2 ) h.1 ⟩, fun h => ⟨ ne_of_lt h.2, h.1 ⟩ ⟩;
  · unfold proj uH; simp_all +decide [ Finset.ext_iff ] ;
    simp_all +decide [ show I = ∅ by ext; aesop ];
    unfold pOn; norm_num [ Finset.image_const, hA ] ;
    rw [ div_self <| Nat.cast_ne_zero.mpr hA.card_pos.ne', Real.negMulLog_one ]

theorem uCondH_anti (A : Finset (Cube m)) (hA : A.Nonempty) (t : Fin m)
    {S T : Finset (Fin m)} (hST : S ⊆ T) :
    uCondH A (coord t) (proj T) ≤ uCondH A (coord t) (proj S) := by
  have := @uCondH_bool_eq_uE_binEntropy;
  convert this A hA ( coord t ) ( fun x => proj T x ) |> le_of_eq |> le_trans <| ?_ using 1;
  rw [ this A hA ( coord t ) ( fun x => proj S x ) ];
  -- By the properties of the projection and the definition of $pOn$, we can group the sum over $A$ by the $S$-fiber.
  have h_group : ∑ x ∈ A, H (pOn ({y ∈ A | proj T y = proj T x}) (coord t) true) ≤ ∑ c ∈ A.image (proj S), ∑ x ∈ A.filter (fun y => proj S y = c), H (pOn ({y ∈ A.filter (fun y => proj S y = c) | proj T y = proj T x}) (coord t) true) := by
    rw [ Finset.sum_image' ];
    intro i hi;
    refine' Finset.sum_congr rfl fun x hx => _;
    congr 2 with y ; simp_all +decide [ Finset.ext_iff, proj ];
    grind;
  -- By the properties of the projection and the definition of $pOn$, we can group the sum over $A$ by the $T$-fiber.
  have h_group_T : ∀ c ∈ A.image (proj S), ∑ x ∈ A.filter (fun y => proj S y = c), H (pOn ({y ∈ A.filter (fun y => proj S y = c) | proj T y = proj T x}) (coord t) true) ≤ (A.filter (fun y => proj S y = c)).card * H (pOn (A.filter (fun y => proj S y = c)) (coord t) true) := by
    intros c hc
    have h_group_T : ∑ x ∈ A.filter (fun y => proj S y = c), H (pOn ({y ∈ A.filter (fun y => proj S y = c) | proj T y = proj T x}) (coord t) true) ≤ ∑ d ∈ (A.filter (fun y => proj S y = c)).image (proj T), (Finset.filter (fun y => proj T y = d) (A.filter (fun y => proj S y = c))).card * H (pOn (Finset.filter (fun y => proj T y = d) (A.filter (fun y => proj S y = c))) (coord t) true) := by
      rw [ Finset.sum_image' ];
      simp +contextual [ Finset.sum_filter ];
      simp +contextual [ Finset.sum_ite ];
    refine le_trans h_group_T ?_;
    have h_jensen : ∀ {w : Finset (Cube m)} (hw : w.Nonempty), ∑ d ∈ w.image (proj T), (Finset.filter (fun y => proj T y = d) w).card * H (pOn (Finset.filter (fun y => proj T y = d) w) (coord t) true) ≤ w.card * H (∑ d ∈ w.image (proj T), (Finset.filter (fun y => proj T y = d) w).card / w.card * pOn (Finset.filter (fun y => proj T y = d) w) (coord t) true) := by
      intros w hw_nonempty
      have h_jensen : ConcaveOn ℝ (Set.Icc 0 1) H := by
        exact Real.strictConcave_binEntropy.concaveOn;
      have h_jensen : ∑ d ∈ w.image (proj T), (Finset.filter (fun y => proj T y = d) w).card / w.card * H (pOn (Finset.filter (fun y => proj T y = d) w) (coord t) true) ≤ H (∑ d ∈ w.image (proj T), (Finset.filter (fun y => proj T y = d) w).card / w.card * pOn (Finset.filter (fun y => proj T y = d) w) (coord t) true) := by
        apply_rules [ h_jensen.le_map_sum ];
        · exact fun _ _ => div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ );
        · rw [ ← Finset.sum_div, div_eq_iff ] <;> norm_cast <;> norm_num [ hw_nonempty.ne_empty ];
          rw [ ← Finset.card_eq_sum_card_fiberwise ];
          exact fun x hx => Finset.mem_image_of_mem _ hx;
        · exact fun x hx => ⟨ pOn_nonneg _ _ _, pOn_le_one _ _ _ ⟩;
      convert mul_le_mul_of_nonneg_left h_jensen ( Nat.cast_nonneg w.card ) using 1;
      simp +decide [ div_eq_inv_mul, mul_assoc, Finset.mul_sum _ _ _, hw_nonempty.ne_empty ];
    convert h_jensen _ using 2;
    · simp +decide [ pOn ];
      rw [ ← Finset.sum_congr rfl fun x hx => by rw [ div_mul_div_comm, mul_comm ] ];
      rw [ Finset.sum_congr rfl fun x hx => by rw [ mul_div_mul_right _ _ ( Nat.cast_ne_zero.mpr <| ne_of_gt <| Finset.card_pos.mpr <| by obtain ⟨ y, hy, rfl ⟩ := Finset.mem_image.mp hx; exact ⟨ y, by aesop ⟩ ) ] ];
      rw [ ← Finset.sum_div _ _ _, ← Nat.cast_sum ];
      rw [ ← Finset.card_biUnion ];
      · congr with x ; simp +decide [ Finset.mem_biUnion ];
        grind;
      · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
    · exact Exists.elim ( Finset.mem_image.mp hc ) fun x hx => ⟨ x, by aesop ⟩;
  convert div_le_div_of_nonneg_right h_group ( Nat.cast_nonneg A.card ) |> le_trans <| div_le_div_of_nonneg_right ( Finset.sum_le_sum h_group_T ) ( Nat.cast_nonneg A.card ) using 1;
  unfold uE;
  rw [ Finset.sum_image' ];
  intro x hx; rw [ Finset.sum_congr rfl fun y hy => by rw [ Finset.mem_filter.mp hy |>.2 ] ] ; simp +decide [ Finset.sum_const, nsmul_eq_mul ] ;

theorem sum_hstep_le_uH_proj (A : Finset (Cube m)) (hA : A.Nonempty)
    (I : Finset (Fin m)) :
    ∑ t ∈ I, hstep A t ≤ uH A (proj I) := by
  rw [ HarperStability.uH_proj_chain A hA I ];
  apply Finset.sum_le_sum;
  exact fun t ht => HarperStability.uCondH_anti A hA t ( Finset.filter_subset_filter _ <| Finset.subset_univ _ )

/-- Independent-window probability restricted to an ambient coordinate set. -/
noncomputable def windowProbWithin {m : ℕ} (U J : Finset (Fin m)) (p : ℝ) : ℝ :=
  p ^ J.card * (1 - p) ^ (U.card - J.card)

theorem windowProb_nonneg (J : Finset (Fin m)) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ windowProb J p := by
  unfold windowProb
  exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)

theorem sum_windowProb_eq_one (p : ℝ) (_hp0 : 0 ≤ p) (_hp1 : p ≤ 1) :
    (∑ J : Finset (Fin m), windowProb J p) = 1 := by
  classical
  unfold windowProb
  simpa [Fintype.card_fin] using
    (Fintype.sum_pow_mul_eq_add_pow (Fin m) p (1 - p) :
      (∑ J : Finset (Fin m), p ^ J.card * (1 - p) ^ (Fintype.card (Fin m) - J.card)) =
        (p + (1 - p)) ^ Fintype.card (Fin m))

theorem windowProb_split_below (J : Finset (Fin m)) (t : Fin m) (p : ℝ) :
    windowProb J p =
      windowProbWithin (below (Finset.univ : Finset (Fin m)) t)
        (J ∩ below (Finset.univ : Finset (Fin m)) t) p *
      windowProbWithin ((Finset.univ : Finset (Fin m)) \ below (Finset.univ : Finset (Fin m)) t)
        (J \ below (Finset.univ : Finset (Fin m)) t) p := by
  classical
  let U : Finset (Fin m) := below (Finset.univ : Finset (Fin m)) t
  let V : Finset (Fin m) := (Finset.univ : Finset (Fin m)) \ U
  unfold windowProb windowProbWithin
  change p ^ J.card * (1 - p) ^ (m - J.card) =
    (p ^ (J ∩ U).card * (1 - p) ^ (U.card - (J ∩ U).card)) *
      (p ^ (J \ U).card * (1 - p) ^ (V.card - (J \ U).card))
  have hJ : (J ∩ U).card + (J \ U).card = J.card :=
    Finset.card_inter_add_card_sdiff J U
  have hU : U.card + V.card = m := by
    have hsub : U ⊆ (Finset.univ : Finset (Fin m)) := by
      intro x _
      simp
    have h := Finset.card_sdiff_add_card_eq_card hsub
    simpa [V, Fintype.card_fin, Nat.add_comm] using h
  have hJU : (J ∩ U).card ≤ U.card := by
    exact Finset.card_le_card (by
      intro x hx
      exact (Finset.mem_inter.mp hx).2)
  have hJV : (J \ U).card ≤ V.card := by
    exact Finset.card_le_card (by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      rw [Finset.mem_sdiff]
      exact ⟨by simp, hx.2⟩)
  have hExp : (U.card - (J ∩ U).card) + (V.card - (J \ U).card) =
      m - J.card := by
    omega
  have hExp' : (U.card - (J ∩ U).card) + (V.card - (J \ U).card) =
      m - ((J ∩ U).card + (J \ U).card) := by
    omega
  rw [← hJ, ← hExp', pow_add, pow_add]
  ring

private lemma sum_filter_t_in (t : Fin m) (f : Finset (Fin m) → ℝ) :
    (∑ J ∈ Finset.univ.filter (fun J : Finset (Fin m) => t ∈ J), f J) =
    (∑ K ∈ Finset.univ.filter (fun J : Finset (Fin m) => t ∉ J), f (insert t K)) := by
  apply Finset.sum_bij (fun J _ => J \ {t})
  · intro J hJ
    rw [Finset.mem_filter] at hJ ⊢
    exact ⟨Finset.mem_univ _, by simp⟩
  · intro J1 hJ1 J2 hJ2 heq
    rw [Finset.mem_filter] at hJ1 hJ2
    have h1 : J1 = insert t (J1 \ {t}) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · intro hx
        rcases eq_or_ne x t with rfl | hne
        · exact Or.inl rfl
        · exact Or.inr ⟨hx, hne⟩
      · rintro (rfl | ⟨hx, _⟩)
        · exact hJ1.2
        · exact hx
    have h2 : J2 = insert t (J2 \ {t}) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · intro hx
        rcases eq_or_ne x t with rfl | hne
        · exact Or.inl rfl
        · exact Or.inr ⟨hx, hne⟩
      · rintro (rfl | ⟨hx, _⟩)
        · exact hJ2.2
        · exact hx
    rw [h1, h2, heq]
  · intro K hK
    rw [Finset.mem_filter] at hK
    refine ⟨insert t K, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Finset.mem_insert_self t K⟩
    · ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | hx, hne⟩
        · contradiction
        · exact hx
      · intro hx
        exact ⟨Or.inr hx, by rintro rfl; exact hK.2 hx⟩
  · intro J hJ
    rw [Finset.mem_filter] at hJ
    have h1 : insert t (J \ {t}) = J := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · rintro (rfl | ⟨hx, _⟩)
        · exact hJ.2
        · exact hx
      · intro hx
        rcases eq_or_ne x t with rfl | hne
        · exact Or.inl rfl
        · exact Or.inr ⟨hx, hne⟩
    rw [h1]

private theorem windowProb_insert {t : Fin m} {K : Finset (Fin m)} (hK : t ∉ K) (p : ℝ) :
    windowProb (insert t K) p = p * (windowProb (insert t K) p + windowProb K p) := by
  unfold windowProb
  have h_card : (insert t K).card = K.card + 1 := by simp [hK]
  rw [h_card]
  have h_le : K.card + 1 ≤ m := by
    have h_card_univ : (insert t K).card ≤ Fintype.card (Fin m) := Finset.card_le_univ (insert t K)
    have hm : Fintype.card (Fin m) = m := Fintype.card_fin m
    rw [hm] at h_card_univ
    omega
  have h_pow1 : (1 - p) ^ (m - K.card) = (1 - p) ^ (m - (K.card + 1)) * (1 - p) := by
    have h1 : m - K.card = m - (K.card + 1) + 1 := by omega
    rw [h1, pow_add, pow_one]
  rw [h_pow1]
  calc
    p ^ (K.card + 1) * (1 - p) ^ (m - (K.card + 1)) = p * p ^ K.card * (1 - p) ^ (m - (K.card + 1)) := by
      have h_pow2 : p ^ (K.card + 1) = p * p ^ K.card := by rw [pow_add, pow_one, mul_comm]
      rw [h_pow2]
    _ = p * (p ^ K.card * (1 - p) ^ (m - (K.card + 1))) := by ring
    _ = p * (p ^ K.card * (1 - p) ^ (m - (K.card + 1)) * 1) := by rw [mul_one]
    _ = p * (p ^ K.card * (1 - p) ^ (m - (K.card + 1)) * (p + (1 - p))) := by ring
    _ = p * (p ^ (K.card + 1) * (1 - p) ^ (m - (K.card + 1)) + p ^ K.card * ((1 - p) ^ (m - (K.card + 1)) * (1 - p))) := by
      have h_pow3 : p ^ (K.card + 1) = p ^ K.card * p := by rw [pow_add, pow_one]
      rw [h_pow3]
      ring

theorem windowProb_mem_past_independent (t : Fin m) (p : ℝ)
    (g : Finset (Fin m) → ℝ) :
    (∑ J : Finset (Fin m),
        windowProb J p *
          (if t ∈ J then
            g (J ∩ below (Finset.univ : Finset (Fin m)) t)
          else 0)) =
      p * (∑ J : Finset (Fin m),
        windowProb J p *
          g (J ∩ below (Finset.univ : Finset (Fin m)) t)) := by
  let U := below (Finset.univ : Finset (Fin m)) t
  have h_t_not_below : t ∉ U := by simp [U, below]

  have h_LHS : (∑ J : Finset (Fin m), windowProb J p * (if t ∈ J then g (J ∩ U) else 0)) =
      ∑ K ∈ Finset.univ.filter (fun J => t ∉ J), windowProb (insert t K) p * g (K ∩ U) := by
    have h_split : (∑ J : Finset (Fin m), windowProb J p * (if t ∈ J then g (J ∩ U) else 0)) =
      (∑ J ∈ Finset.univ.filter (fun J => t ∈ J), windowProb J p * (if t ∈ J then g (J ∩ U) else 0)) +
      (∑ J ∈ Finset.univ.filter (fun J => t ∉ J), windowProb J p * (if t ∈ J then g (J ∩ U) else 0)) := by
      exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun J => t ∈ J) _).symm
    rw [h_split]
    have h_not : (∑ J ∈ Finset.univ.filter (fun J => t ∉ J), windowProb J p * (if t ∈ J then g (J ∩ U) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro J hJ
      rw [Finset.mem_filter] at hJ
      have h_if : (if t ∈ J then g (J ∩ U) else 0) = 0 := if_neg hJ.2
      rw [h_if, mul_zero]
    rw [h_not, add_zero]
    have h_in : (∑ J ∈ Finset.univ.filter (fun J => t ∈ J), windowProb J p * (if t ∈ J then g (J ∩ U) else 0)) =
        ∑ J ∈ Finset.univ.filter (fun J => t ∈ J), windowProb J p * g (J ∩ U) := by
      apply Finset.sum_congr rfl
      intro J hJ
      rw [Finset.mem_filter] at hJ
      rw [if_pos hJ.2]
    rw [h_in]
    rw [sum_filter_t_in]
    apply Finset.sum_congr rfl
    intro K hK
    rw [Finset.mem_filter] at hK
    have h_inter : insert t K ∩ U = K ∩ U := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, hU⟩
        · contradiction
        · exact ⟨hx, hU⟩
      · rintro ⟨hx, hU⟩
        exact ⟨Or.inr hx, hU⟩
    rw [h_inter]

  have h_RHS : p * (∑ J : Finset (Fin m), windowProb J p * g (J ∩ U)) =
      ∑ K ∈ Finset.univ.filter (fun J => t ∉ J), p * (windowProb (insert t K) p + windowProb K p) * g (K ∩ U) := by
    have h_split : (∑ J : Finset (Fin m), windowProb J p * g (J ∩ U)) =
      (∑ J ∈ Finset.univ.filter (fun J => t ∈ J), windowProb J p * g (J ∩ U)) +
      (∑ J ∈ Finset.univ.filter (fun J => t ∉ J), windowProb J p * g (J ∩ U)) := by
      exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun J => t ∈ J) _).symm
    rw [h_split]
    rw [sum_filter_t_in]
    rw [← Finset.sum_add_distrib]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro K hK
    rw [Finset.mem_filter] at hK
    have h_inter : insert t K ∩ U = K ∩ U := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hx, hU⟩
        · contradiction
        · exact ⟨hx, hU⟩
      · rintro ⟨hx, hU⟩
        exact ⟨Or.inr hx, hU⟩
    rw [h_inter]
    ring

  rw [h_LHS, h_RHS]
  apply Finset.sum_congr rfl
  intro K hK
  rw [Finset.mem_filter] at hK
  have h_prob : windowProb (insert t K) p = p * (windowProb (insert t K) p + windowProb K p) := windowProb_insert hK.2 p
  nth_rw 1 [h_prob]

/-
Binary entropy is `4`-strongly concave on `[0,1]`: the perturbed function
`binEntropy x + 2 x^2` is concave (since `binEntropy'' x = -1/(x(1-x)) ≤ -4`).
-/
theorem concaveOn_binEntropy_add_two_sq :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun x => Real.binEntropy x + 2 * x ^ 2) := by
  apply_rules [ concaveOn_of_deriv2_nonpos, convex_Icc ];
  · exact ContinuousOn.add ( Real.binEntropy_continuous.continuousOn ) ( continuousOn_const.mul ( continuousOn_pow 2 ) );
  · norm_num [ DifferentiableOn ];
    exact fun x hx₁ hx₂ => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.add ( Real.differentiableAt_binEntropy hx₁.ne' hx₂.ne ) ( by norm_num ) );
  · norm_num [ interior_Icc ];
    refine' DifferentiableOn.congr _ _;
    exact fun x => Real.log ( 1 - x ) - Real.log x + 4 * x;
    · exact DifferentiableOn.add ( DifferentiableOn.sub ( DifferentiableOn.log ( differentiableOn_id.const_sub _ ) ( by intro x hx; linarith [ hx.1, hx.2 ] ) ) ( DifferentiableOn.log ( differentiableOn_id ) ( by intro x hx; linarith [ hx.1, hx.2 ] ) ) ) ( differentiableOn_id.const_mul _ );
    · intro x hx; rw [ show deriv ( fun x => Real.binEntropy x + 2 * x ^ 2 ) x = deriv ( fun x => Real.binEntropy x ) x + deriv ( fun x => 2 * x ^ 2 ) x from deriv_add ( by exact Real.differentiableAt_binEntropy ( ne_of_gt hx.1 ) ( ne_of_lt hx.2 ) ) ( by norm_num ) ] ; norm_num [ Real.deriv_binEntropy, hx.1.ne', hx.2.ne ] ; ring;
  · -- Let's calculate the second derivative of the function $f(x) = \text{binEntropy}(x) + 2x^2$.
    have h_second_deriv : ∀ x ∈ Set.Ioo 0 1, deriv^[2] (fun x => Real.binEntropy x + 2 * x ^ 2) x = deriv (fun x => Real.log (1 - x) - Real.log x + 4 * x) x := by
      intros x hx
      have h_deriv1 : ∀ x ∈ Set.Ioo 0 1, deriv (fun x => Real.binEntropy x + 2 * x ^ 2) x = Real.log (1 - x) - Real.log x + 4 * x := by
        intro x hx; refine' HasDerivAt.deriv _; convert HasDerivAt.add ( Real.hasDerivAt_binEntropy hx.1.ne' hx.2.ne ) ( HasDerivAt.const_mul 2 ( hasDerivAt_pow 2 x ) ) using 1 ; ring;
      exact Filter.EventuallyEq.deriv_eq ( Filter.eventuallyEq_of_mem ( Ioo_mem_nhds hx.1 hx.2 ) h_deriv1 );
    simp_all +decide [ mul_comm ];
    intro x hx₁ hx₂; erw [ deriv_add, deriv_sub ] <;> norm_num [ hx₁.ne', hx₂.ne', sub_ne_zero.mpr hx₂.ne' ];
    · erw [ deriv.log, deriv_sub ] <;> norm_num;
      · rw [ div_sub', div_add', div_le_iff₀ ] <;> nlinarith [ sq_nonneg ( x - 1 / 2 ), mul_inv_cancel₀ hx₁.ne' ];
      · exact differentiableAt_id.const_sub _;
      · linarith;
    · exact DifferentiableAt.log ( differentiableAt_id.const_sub _ ) ( by linarith );
    · exact DifferentiableAt.log ( differentiableAt_id.const_sub _ ) ( by linarith )

theorem binary_entropy_jensen_gap (A : Finset (Cube m)) (hA : A.Nonempty)
    (r : Cube m → ℝ)
    (hr0 : ∀ x ∈ A, 0 ≤ r x) (hr1 : ∀ x ∈ A, r x ≤ 1) :
    H (uE A r) - uE A (fun x => H (r x)) ≥ 2 * varOn A r := by
  have h_jensen : (∑ x ∈ A, (1 / A.card : ℝ) • (H (r x) + 2 * (r x) ^ 2)) ≤ H (∑ x ∈ A, (1 / A.card : ℝ) • r x) + 2 * (∑ x ∈ A, (1 / A.card : ℝ) • r x) ^ 2 := by
    have h_jensen : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun x => H x + 2 * x ^ 2) := by
      convert concaveOn_binEntropy_add_two_sq using 1;
    convert h_jensen.le_map_sum _ _ _ <;> norm_num [ hA.ne_empty ];
    aesop;
  unfold uE varOn; simp_all +decide ; ring_nf at *;
  unfold uE; simp_all +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _ ] ; ring_nf at *;
  simp_all +decide [ ← Finset.sum_mul, pow_three, sq, mul_assoc, mul_comm, mul_left_comm, hA.ne_empty ];
  simp_all +decide [ ← mul_assoc, ← Finset.sum_mul _ _ _ ] ; linarith

/-
Quantitative refinement gap (strong-concavity version of `uCondH_anti`):
for `S ⊆ T`, refining the conditioning window from `S` to `T` decreases the
conditional entropy by at least twice the conditional variance of the
`T`-fiber branching probability, measured across the `S`-conditioning.
-/
set_option maxHeartbeats 2000000 in
theorem uCondH_gap_ge_two_uCondVar (A : Finset (Cube m)) (hA : A.Nonempty)
    (t : Fin m) {S T : Finset (Fin m)} (hST : S ⊆ T) :
    uCondH A (coord t) (proj S) - uCondH A (coord t) (proj T) ≥
      2 * uCondVar A
        (fun x => pOn (A.filter fun y => proj T y = proj T x) (coord t) true)
        (proj S) := by
  -- Apply the binary entropy Jensen gap lemma to each term in the sum.
  have h_jensen : ∀ c ∈ A.image (proj S), (A.filter fun y => proj S y = c).card * H (pOn (A.filter fun y => proj S y = c) (coord t) true) - ∑ x ∈ A.filter fun y => proj S y = c, H (pOn (A.filter fun y => proj T y = proj T x) (coord t) true) ≥ 2 * ((A.filter fun y => proj S y = c).card * varOn (A.filter fun y => proj S y = c) (fun x => pOn (A.filter fun y => proj T y = proj T x) (coord t) true)) := by
    intro c hc
    have h_jensen_gap : H (pOn (A.filter fun y => proj S y = c) (coord t) true) - uE (A.filter fun y => proj S y = c) (fun x => H (pOn (A.filter fun y => proj T y = proj T x) (coord t) true)) ≥ 2 * varOn (A.filter fun y => proj S y = c) (fun x => pOn (A.filter fun y => proj T y = proj T x) (coord t) true) := by
      convert binary_entropy_jensen_gap _ _ _ _ _ using 1;
      · rw [ show uE ( Finset.filter ( fun y => proj S y = c ) A ) ( fun x => pOn ( Finset.filter ( fun y => proj T y = proj T x ) A ) ( coord t ) true ) = pOn ( Finset.filter ( fun y => proj S y = c ) A ) ( coord t ) true from ?_ ];
        have h_fiber : ∀ d ∈ (A.filter (fun y => proj S y = c)).image (proj T), (∑ x ∈ (A.filter (fun y => proj S y = c)).filter (fun y => proj T y = d), pOn (A.filter (fun y => proj T y = proj T x)) (coord t) true) = (A.filter (fun y => proj T y = d) |>.filter (fun y => coord t y)).card := by
          intros d hd
          have h_fiber : ∀ x ∈ (A.filter (fun y => proj S y = c)).filter (fun y => proj T y = d), pOn (A.filter (fun y => proj T y = proj T x)) (coord t) true = (A.filter (fun y => proj T y = d) |>.filter (fun y => coord t y)).card / (A.filter (fun y => proj T y = d)).card := by
            simp +contextual [ pOn ];
            grind;
          rw [ Finset.sum_congr rfl h_fiber, Finset.sum_const, Finset.card_eq_sum_ones ] ; norm_num;
          rw [ mul_div, div_eq_iff ] <;> norm_cast <;> simp_all +decide [ Finset.ext_iff ];
          · rw [ mul_comm ];
            congr! 1;
            congr 1 with x ; simp +contextual ;
            intro hx hx' a; have := hd.choose_spec.2 a; simp_all +decide [ proj ] ;
            grind;
          · exact ⟨ hd.choose, hd.choose_spec.1.1, hd.choose_spec.2 ⟩;
        have h_fiber_sum : ∑ x ∈ A.filter (fun y => proj S y = c), pOn (A.filter (fun y => proj T y = proj T x)) (coord t) true = (A.filter (fun y => proj S y = c) |>.filter (fun y => coord t y)).card := by
          convert Finset.sum_congr rfl h_fiber using 1;
          · rw [ Finset.sum_image' ] ; aesop;
          · rw_mod_cast [ Finset.card_filter ];
            rw [ Finset.sum_image' ];
            simp +contextual [ Finset.filter_filter ];
            intro i hi hi'; congr 1 with j ; simp +contextual ;
            intro hj hj' hj''; rw [ ← hi' ] ; ext x; simp_all +decide [ Finset.subset_iff, proj ] ;
            replace hj'' := Finset.ext_iff.mp hj'' x; aesop;
        unfold uE pOn; simp +decide ;
        convert congr_arg ( fun x : ℝ => x / ( A.filter ( fun y => proj S y = c ) |> Finset.card : ℝ ) ) h_fiber_sum using 1;
        convert rfl;
      · exact Exists.elim ( Finset.mem_image.mp hc ) fun x hx => ⟨ x, by aesop ⟩;
      · exact fun x hx => pOn_nonneg _ _ _;
      · exact fun x hx => pOn_le_one _ _ _;
    simp_all +decide [ uE, mul_comm ];
    rw [ sub_div', le_div_iff₀ ] at h_jensen_gap <;> nlinarith [ show ( Finset.card ( Finset.filter ( fun y => proj S y = c ) A ) : ℝ ) > 0 from Nat.cast_pos.mpr ( Finset.card_pos.mpr ⟨ hc.choose, Finset.mem_filter.mpr ⟨ hc.choose_spec.1, hc.choose_spec.2 ⟩ ⟩ ) ];
  have h_sum_jensen : (A.card : ℝ) * (uE A (fun x => H (pOn (A.filter fun y => proj S y = proj S x) (coord t) true)) - uE A (fun x => H (pOn (A.filter fun y => proj T y = proj T x) (coord t) true))) ≥ 2 * (A.card : ℝ) * uCondVar A (fun x => pOn (A.filter fun y => proj T y = proj T x) (coord t) true) (proj S) := by
    have h_sum_jensen : (A.card : ℝ) * (uE A (fun x => H (pOn (A.filter fun y => proj S y = proj S x) (coord t) true)) - uE A (fun x => H (pOn (A.filter fun y => proj T y = proj T x) (coord t) true))) = ∑ c ∈ A.image (proj S), ((A.filter fun y => proj S y = c).card * H (pOn (A.filter fun y => proj S y = c) (coord t) true) - ∑ x ∈ A.filter fun y => proj S y = c, H (pOn (A.filter fun y => proj T y = proj T x) (coord t) true)) := by
      unfold uE; simp +decide [ Finset.sum_sub_distrib, mul_sub ] ;
      rw [ mul_div_cancel₀ _ ( Nat.cast_ne_zero.mpr hA.card_pos.ne' ), Finset.sum_image' ];
      rw [ mul_div_cancel₀ _ ( Nat.cast_ne_zero.mpr hA.card_pos.ne' ), Finset.sum_image' ];
      · exact fun _ _ => rfl;
      · intro x hx; rw [ Finset.sum_congr rfl fun y hy => by rw [ Finset.mem_filter.mp hy |>.2 ] ] ; simp +decide ;
    rw [h_sum_jensen];
    refine' le_trans _ ( Finset.sum_le_sum h_jensen );
    unfold uCondVar;
    simp +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, pOn ];
    field_simp;
    grind;
  simp_all +decide [ uE, uCondVar, uCondH_bool_eq_uE_binEntropy ];
  nlinarith [ show ( A.card : ℝ ) > 0 by exact Nat.cast_pos.mpr hA.card_pos ]

theorem observer_surplus_lemma (A : Finset (Cube m)) (hA : A.Nonempty)
    (W : Finset (Fin m)) :
    uH A (proj W) - ∑ t ∈ W, hstep A t ≥
      2 * ∑ t ∈ W,
        uCondVar A
          (fun x => rho A t (proj (below (Finset.univ : Finset (Fin m)) t) x))
          (proj (below W t)) := by
  rw [uH_proj_chain A hA W]
  unfold hstep
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  have hsub : below W t ⊆ below (Finset.univ : Finset (Fin m)) t :=
    Finset.filter_subset_filter _ (Finset.subset_univ _)
  have hgap := uCondH_gap_ge_two_uCondVar A hA t hsub
  exact hgap

/-
Coarsening reduces entropy: applying a function `ψ` to a statistic `h`
cannot increase the entropy.
-/
theorem uH_comp_le {D E : Type*} [DecidableEq D] [DecidableEq E]
    (A : Finset (Cube m)) (h : Cube m → D) (ψ : D → E) :
    uH A (fun x => ψ (h x)) ≤ uH A h := by
  convert Finset.sum_le_sum ?_ using 1;
  rotate_left;
  use fun e => ∑ d ∈ Finset.image h A |>.filter ( fun d => ψ d = e ), Real.negMulLog ( pOn A h d );
  · infer_instance;
  · intro e he
    have h_group : pOn A (fun x => ψ (h x)) e = ∑ d ∈ Finset.image h A |>.filter (fun d => ψ d = e), pOn A h d := by
      unfold pOn;
      rw [ ← Finset.sum_div _ _ _, eq_comm ];
      rw [ ← Nat.cast_sum, ← Finset.card_biUnion ];
      · congr with x ; aesop;
      · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
    have h_superadd : ∀ (s : Finset D) (q : D → ℝ), (∀ d ∈ s, 0 ≤ q d) → Real.negMulLog (∑ d ∈ s, q d) ≤ ∑ d ∈ s, Real.negMulLog (q d) := by
      intro s q hq_nonneg
      have h_superadd : ∀ d ∈ s, Real.negMulLog (q d) ≥ q d * (-Real.log (∑ d ∈ s, q d)) := by
        intro d hd; by_cases hq_zero : q d = 0 <;> simp_all +decide [ Real.negMulLog ] ;
        exact mul_le_mul_of_nonneg_left ( Real.log_le_log ( lt_of_le_of_ne ( hq_nonneg d hd ) ( Ne.symm hq_zero ) ) ( Finset.single_le_sum ( fun x _ => hq_nonneg x ‹_› ) hd ) ) ( hq_nonneg d hd );
      refine' le_trans _ ( Finset.sum_le_sum h_superadd );
      rw [ ← Finset.sum_mul _ _ _ ] ; unfold Real.negMulLog ; aesop;
    exact h_group.symm ▸ h_superadd _ _ fun d hd => pOn_nonneg _ _ _;
  · rw [ ← Finset.sum_biUnion ];
    · refine' Finset.sum_bij ( fun x hx => x ) _ _ _ _ <;> simp +decide;
      exact fun x hx => ⟨ ⟨ x, hx, rfl ⟩, ⟨ x, hx, rfl ⟩ ⟩;
    · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;

/-
Fiber decomposition of joint minus marginal entropy (general chain-rule
identity): `H(f,g) - H(g)` equals the `g`-fiber-averaged within-fiber entropy
of `f`.
-/
theorem uH_prod_sub_eq_sum {D E : Type*} [DecidableEq D] [DecidableEq E]
    (A : Finset (Cube m)) (hA : A.Nonempty) (f : Cube m → D) (g : Cube m → E) :
    uH A (fun x => (f x, g x)) - uH A g =
      ∑ c ∈ A.image g, pOn A g c *
        (∑ b ∈ A.image f, Real.negMulLog (pOn (A.filter fun y => g y = c) f b)) := by
  have h_split : uH A (fun x => (f x, g x)) = ∑ c ∈ A.image g, ∑ b ∈ A.image f, Real.negMulLog (pOn A (fun x => (f x, g x)) (b, c)) := by
    convert Finset.sum_subset ?_ ?_ using 1;
    rotate_left;
    exact Finset.image f A ×ˢ Finset.image g A;
    · grind;
    · simp +contextual [ pOn ];
      intro a b x hx hx' y hy hy' h; rw [ Finset.card_eq_zero.mpr ] <;> aesop;
    · rw [ Finset.sum_product, Finset.sum_comm ];
  rw [ h_split, sub_eq_iff_eq_add ];
  have h_split : ∀ c ∈ A.image g, ∑ b ∈ A.image f, Real.negMulLog (pOn A (fun x => (f x, g x)) (b, c)) = pOn A g c * ∑ b ∈ A.image f, Real.negMulLog (pOn (A.filter fun y => g y = c) f b) + Real.negMulLog (pOn A g c) := by
    intro c hc
    have h_split : ∀ b ∈ A.image f, Real.negMulLog (pOn A (fun x => (f x, g x)) (b, c)) = pOn A g c * Real.negMulLog (pOn (A.filter fun y => g y = c) f b) + pOn (A.filter fun y => g y = c) f b * Real.negMulLog (pOn A g c) := by
      intro b hb
      have h_split : pOn A (fun x => (f x, g x)) (b, c) = pOn A g c * pOn (A.filter fun y => g y = c) f b := by
        unfold pOn;
        rw [ div_mul_div_comm, div_eq_div_iff ] <;> norm_cast <;> simp +decide [ Finset.filter_filter, Finset.filter_and ];
        · grind;
        · exact hA.ne_empty;
        · exact ⟨ hA.ne_empty, by obtain ⟨ x, hx, rfl ⟩ := Finset.mem_image.mp hc; exact ⟨ x, hx, rfl ⟩ ⟩;
      grind +suggestions;
    rw [ Finset.sum_congr rfl h_split, Finset.sum_add_distrib, Finset.mul_sum _ _ _ ];
    have h_sum_pOn : ∑ b ∈ A.image f, pOn (A.filter fun y => g y = c) f b = 1 := by
      convert sum_pOn_image_eq_one ( A.filter fun y => g y = c ) _ f using 1;
      · rw [ ← Finset.sum_subset ];
        · grind;
        · simp +contextual [ pOn ];
      · exact Exists.elim ( Finset.mem_image.mp hc ) fun x hx => ⟨ x, Finset.mem_filter.mpr ⟨ hx.1, hx.2 ⟩ ⟩;
    simp +decide [ ← Finset.sum_mul, h_sum_pOn ];
  rw [ Finset.sum_congr rfl h_split, Finset.sum_add_distrib, uH ];
  convert rfl

/-
Subadditivity of entropy: the joint entropy of a pair is at most the sum
of the marginal entropies.
-/
theorem uH_prod_le {D E : Type*} [DecidableEq D] [DecidableEq E]
    (A : Finset (Cube m)) (hA : A.Nonempty) (f : Cube m → D) (g : Cube m → E) :
    uH A (fun x => (f x, g x)) ≤ uH A f + uH A g := by
  have h_total_prob : ∀ (b : D), (∑ c ∈ A.image g, pOn A g c * pOn (A.filter fun y => g y = c) f b) = pOn A f b := by
    intro b
    have h_sum : ∑ c ∈ A.image g, ((A.filter (fun y => g y = c)).card : ℝ) * ((A.filter (fun y => g y = c ∧ f y = b)).card : ℝ) / ((A.filter (fun y => g y = c)).card : ℝ) = (A.filter (fun y => f y = b)).card := by
      rw [ Finset.sum_congr rfl fun x hx => by rw [ mul_div_cancel_left₀ _ ( Nat.cast_ne_zero.mpr <| ne_of_gt <| Finset.card_pos.mpr <| by obtain ⟨ y, hy, rfl ⟩ := Finset.mem_image.mp hx; exact ⟨ y, by aesop ⟩ ) ] ];
      rw_mod_cast [ ← Finset.card_biUnion ];
      · congr with x ; aesop;
      · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun z hz₁ hz₂ => hxy <| by aesop;
    convert congr_arg ( fun x : ℝ => x / ( A.card : ℝ ) ) h_sum using 1;
    · rw [ Finset.sum_div _ _ _ ] ; refine' Finset.sum_congr rfl fun x hx => _ ; unfold pOn ; simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, Finset.filter_filter ] ;
      grind;
    · unfold pOn;
      convert rfl;
  rw [ ← sub_le_iff_le_add, uH_prod_sub_eq_sum A hA f g ];
  have h_jensen : ∀ (b : D), (∑ c ∈ A.image g, pOn A g c * Real.negMulLog (pOn (A.filter fun y => g y = c) f b)) ≤ Real.negMulLog (pOn A f b) := by
    intro b;
    convert ( Real.concaveOn_negMulLog.le_map_sum _ _ _ ) using 1;
    · aesop;
    · exact fun _ _ => pOn_nonneg _ _ _;
    · convert sum_pOn_image_eq_one A hA g;
    · exact fun _ _ => pOn_nonneg _ _ _;
  convert Finset.sum_le_sum fun b hb => h_jensen b using 1;
  rw [ Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _ ];
  convert rfl

/-
Coordinatewise subadditivity of entropy for a finite product-valued
statistic.
-/
theorem uH_pi_le_sum {D : Type*} [DecidableEq D] [Inhabited D]
    (A : Finset (Cube m)) (hA : A.Nonempty) (k : Cube m → Fin m → D) :
    uH A k ≤ ∑ t : Fin m, uH A (fun x => k x t) := by
  have h_subadd : ∀ J : Finset (Fin m), uH A (fun x => fun s => if s ∈ J then k x s else default) ≤ ∑ t ∈ J, uH A (fun x => k x t) := by
    intro J;
    induction' J using Finset.induction with t J hJ ih;
    · simp +decide [ uH ];
      rw [ Finset.sum_eq_single ( fun _ => default ) ] <;> simp +decide [ pOn ];
      · simp +decide [ hA.ne_empty, Real.negMulLog ];
      · exact fun h => False.elim ( hA.ne_empty ( Finset.eq_empty_of_forall_notMem h ) );
    · have h_subadd : uH A (fun x => fun s => if s ∈ insert t J then k x s else default) ≤ uH A (fun x => (k x t, fun s => if s ∈ J then k x s else default)) := by
        convert uH_comp_le _ _ _;
        rotate_right;
        use fun p s => if s = t then p.1 else p.2 s;
        · grind;
        · infer_instance;
        · infer_instance;
      have h_subadd : uH A (fun x => (k x t, fun s => if s ∈ J then k x s else default)) ≤ uH A (fun x => k x t) + uH A (fun x => fun s => if s ∈ J then k x s else default) := by
        exact uH_prod_le A hA _ _;
      rw [ Finset.sum_insert hJ ] ; linarith;
  simpa using h_subadd Finset.univ

/-
The entropy of a `Bool`-valued statistic equals the binary entropy of its
true-probability.
-/
theorem uH_bool_eq_binEntropy (A : Finset (Cube m)) (hA : A.Nonempty)
    (f : Cube m → Bool) :
    uH A f = H (pOn A f true) := by
  have h_image : A.image f ⊆ {true, false} := by
    grind +qlia;
  unfold uH;
  have h_sum : ∑ b ∈ Finset.image f A, Real.negMulLog (pOn A f b) = ∑ b ∈ ({true, false} : Finset Bool), Real.negMulLog (pOn A f b) := by
    rw [ ← Finset.sum_subset h_image ];
    intro x hx hx'; unfold pOn; simp_all +decide ;
    rw [ Finset.card_eq_zero.mpr ] <;> aesop;
  convert h_sum using 1;
  · convert rfl;
  · have h_sum : pOn A f true + pOn A f false = 1 := by
      unfold pOn;
      rw [ ← add_div, div_eq_iff ] <;> norm_cast <;> simp +decide [ hA.ne_empty ];
      rw [ Finset.card_filter, Finset.card_filter ] ; rw [ ← Finset.sum_add_distrib ] ; rw [ Finset.sum_congr rfl fun x hx => by aesop ] ; aesop;
    convert Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub ( pOn A f true ) using 1;
    grind

/-- Per-coordinate Fano bound: the entropy of the diff column at coordinate
`t` is at most the binary entropy of the mismatch probability plus the
mismatch probability times `log BSize`. -/
theorem uH_diff_col_le {B : Type*} [DecidableEq B] (A : Finset (Cube m))
    (hA : A.Nonempty) (F G : Cube m → Fin m → B) (t : Fin m) (BSize : ℝ)
    (hBSize : 1 ≤ BSize)
    (hSize : ((A.image fun x => F x t).card : ℝ) ≤ BSize) :
    uH A (fun x => if F x t = G x t then (none : Option B) else some (F x t)) ≤
      H (pOn A (fun x => decide (F x t ≠ G x t)) true) +
        pOn A (fun x => decide (F x t ≠ G x t)) true * Real.log BSize := by
  have h_ind : uH A (fun x => decide (F x t ≠ G x t)) = H (pOn A (fun x => decide (F x t ≠ G x t)) true) :=
    uH_bool_eq_binEntropy A hA (fun x => decide (F x t ≠ G x t));
  have h_prod : uH A (fun x => (if F x t = G x t then none else some (F x t), decide (F x t ≠ G x t))) - uH A (fun x => decide (F x t ≠ G x t)) ≤ pOn A (fun x => decide (F x t ≠ G x t)) true * Real.log BSize := by
    have h_prod : uH A (fun x => (if F x t = G x t then none else some (F x t), decide (F x t ≠ G x t))) - uH A (fun x => decide (F x t ≠ G x t)) ≤ pOn A (fun x => decide (F x t ≠ G x t)) true * uH (A.filter fun y => decide (F y t ≠ G y t)) (fun x => if F x t = G x t then none else some (F x t)) := by
      have h_prod : uH A (fun x => (if F x t = G x t then none else some (F x t), decide (F x t ≠ G x t))) - uH A (fun x => decide (F x t ≠ G x t)) = ∑ c ∈ A.image (fun x => decide (F x t ≠ G x t)), pOn A (fun x => decide (F x t ≠ G x t)) c * uH (A.filter fun y => decide (F y t ≠ G y t) = c) (fun x => if F x t = G x t then none else some (F x t)) := by
        convert uH_prod_sub_eq_sum A hA _ _ using 1;
        all_goals try infer_instance;
        refine' Finset.sum_congr rfl fun c hc => _;
        refine' congr_arg _ ( Finset.sum_subset _ _ );
        · grind +locals;
        · simp +contextual [ pOn ];
          intro a ha h; rw [ Finset.card_eq_zero.mpr ] <;> aesop;
      rw [h_prod];
      rw [ Finset.sum_eq_single true ] <;> simp +contextual ;
      · intro x hx hx'; right; simp +decide [ uH ] ;
        rw [ Finset.sum_eq_single none ] <;> simp +contextual [ pOn ];
        · simp +decide [ Finset.filter_filter ];
          rw [ div_self ] <;> norm_num [ Real.negMulLog_one ] ; aesop;
        · exact fun h => False.elim ( h x hx hx' );
      · intro h; simp +decide [ pOn ] ;
        grind;
    refine' le_trans h_prod ( mul_le_mul_of_nonneg_left _ ( pOn_nonneg _ _ _ ) );
    by_cases h : ( A.filter fun y => decide ( F y t ≠ G y t ) = true ).Nonempty <;> simp_all +decide ;
    · refine' le_trans ( uH_le_log_card_image _ h _ ) _;
      gcongr;
      refine' le_trans _ hSize;
      refine' mod_cast le_trans ( Finset.card_le_card _ ) _;
      exact Finset.image ( fun x => some x ) ( Finset.image ( fun x => F x t ) A );
      · grind;
      · exact Finset.card_image_le;
    · simp_all +decide [ Finset.filter_eq_empty_iff.mpr ];
      exact le_trans ( by unfold uH; norm_num ) ( Real.log_nonneg hBSize );
  convert sub_le_iff_le_add.mp h_prod using 1;
  · refine' le_antisymm _ _;
    · convert uH_comp_le A ( fun x => ( if F x t = G x t then none else some ( F x t ), decide ( F x t ≠ G x t ) ) ) ( fun x => x.1 ) using 1;
    · convert uH_comp_le A ( fun x => if F x t = G x t then none else some ( F x t ) ) ( fun b => ( b, b.isSome ) ) using 1;
      grind;
  · grind

/-
Jensen + monotone-cap combination bounding the total binary entropy of the
coordinatewise mismatch probabilities.
-/
theorem sum_binEntropy_le (δ : Fin m → ℝ) (h0 : ∀ t, 0 ≤ δ t) (h1 : ∀ t, δ t ≤ 1)
    (e : ℝ) (he : 0 ≤ e) (hsum : ∑ t, δ t ≤ e) :
    ∑ t, H (δ t) ≤ (m : ℝ) * H (min (e / (m : ℝ)) (1 / 2)) := by
  rcases eq_or_ne m 0 <;> simp_all +decide;
  · aesop;
  · -- By Jensen's inequality, we have $\sum_{t=0}^{m-1} H(\delta_t) \leq m H(\frac{1}{m} \sum_{t=0}^{m-1} \delta_t)$.
    have h_jensen : ∑ t, H (δ t) ≤ m * H ((∑ t, δ t) / m) := by
      have h_jensen : (∑ t : Fin m, (1 / m : ℝ) • H (δ t)) ≤ H ((∑ t : Fin m, (1 / m : ℝ) • δ t)) := by
        have h_jensen : ConcaveOn ℝ (Set.Icc 0 1) H := by
          have h_concave : StrictConcaveOn ℝ (Set.Icc 0 1) H := by
            exact Real.strictConcave_binEntropy;
          exact h_concave.concaveOn;
        convert h_jensen.le_map_sum _ _ _ <;> aesop;
      simp_all +decide [ div_eq_inv_mul, Finset.mul_sum _ _ _ ];
      simpa [ ← Finset.mul_sum _ _ _, ‹¬m = 0› ] using mul_le_mul_of_nonneg_left h_jensen <| Nat.cast_nonneg m;
    refine le_trans h_jensen ?_;
    by_cases h_case : e / m ≤ 1 / 2;
    · norm_num [ h_case ];
      gcongr;
      apply_rules [ Real.binEntropy_strictMonoOn.monotoneOn ];
      · exact ⟨ div_nonneg ( Finset.sum_nonneg fun _ _ => h0 _ ) ( Nat.cast_nonneg _ ), by norm_num; exact le_trans ( div_le_div_of_nonneg_right hsum ( Nat.cast_nonneg _ ) ) h_case ⟩;
      · exact ⟨ div_nonneg he ( Nat.cast_nonneg _ ), h_case.trans ( by norm_num ) ⟩;
      · gcongr;
    · norm_num [ min_eq_right ( le_of_not_ge h_case ) ];
      exact mul_le_mul_of_nonneg_left ( Real.binEntropy_le_log_two.trans ( by rw [ show H ( 1 / 2 ) = Real.log 2 by exact Real.binEntropy_eq_log_two.mpr <| by norm_num ] ) ) <| Nat.cast_nonneg _

theorem deterministic_field_fano {B : Type*} [DecidableEq B]
    (A : Finset (Cube m)) (hA : A.Nonempty)
    (F G : Cube m → Fin m → B) (e BSize : ℝ)
    (he : 0 ≤ e) (hBSize : 1 ≤ BSize)
    (hSize : ∀ t : Fin m, ((A.image fun x => F x t).card : ℝ) ≤ BSize)
    (hErr : uE A (fun x =>
      (((Finset.univ : Finset (Fin m)).filter fun t => F x t ≠ G x t).card : ℝ)) ≤ e) :
    uH A F ≤ uH A G +
      (m : ℝ) * H (min (e / (m : ℝ)) (1 / 2)) + e * Real.log BSize := by
  have h_uH_F_le_uH_G_plus_uH_delta : uH A F ≤ uH A G + uH A (fun x => fun t => if F x t = G x t then (none : Option B) else some (F x t)) := by
    refine' le_trans _ ( uH_prod_le A hA G _ );
    convert uH_comp_le A ( fun x => ( G x, fun t => if F x t = G x t then none else some ( F x t ) ) ) ( fun x => fun t => ( x.2 t ).getD ( x.1 t ) ) using 2 ; aesop;
  -- By definition of $δ$, we have $\sum t, δ t = uE A (fun x => ((Finset.univ.filter fun t => F x t ≠ G x t).card : ℝ))$.
  have h_sum_delta : ∑ t : Fin m, pOn A (fun x => decide (F x t ≠ G x t)) true = uE A (fun x => ((Finset.univ.filter fun t => F x t ≠ G x t).card : ℝ)) := by
    unfold pOn uE;
    simp +decide only [Finset.card_filter];
    simp +decide only [Nat.cast_sum, Finset.sum_div];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by aesop );
  have h_sum_H_delta : ∑ t : Fin m, H (pOn A (fun x => decide (F x t ≠ G x t)) true) ≤ m * H (min (e / m) (1 / 2)) := by
    apply_rules [ sum_binEntropy_le ];
    · exact fun t => pOn_nonneg _ _ _;
    · exact fun t => pOn_le_one A _ _;
    · linarith;
  have h_uH_delta_le_sum_H_delta_plus_sum_delta_log_BSize : uH A (fun x => fun t => if F x t = G x t then (none : Option B) else some (F x t)) ≤ ∑ t : Fin m, H (pOn A (fun x => decide (F x t ≠ G x t)) true) + ∑ t : Fin m, pOn A (fun x => decide (F x t ≠ G x t)) true * Real.log BSize := by
    refine' le_trans ( uH_pi_le_sum A hA _ ) _;
    rw [ ← Finset.sum_add_distrib ];
    exact Finset.sum_le_sum fun t _ => by simpa using uH_diff_col_le A hA F G t BSize hBSize ( hSize t ) ;
  simp_all +decide [ ← Finset.sum_mul _ _ _ ];
  nlinarith [ Real.log_nonneg hBSize ]

end HarperStability