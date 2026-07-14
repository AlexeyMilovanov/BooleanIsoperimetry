import AverageHarperStability.Interface.Definitions
import AverageHarperStability.MGL.Curve
import AverageHarperStability.Probability.Finite

open scoped BigOperators
open Finset Set Filter Topology Classical

namespace AverageHarperStability

/-- Coordinates strictly before `t` in the fixed revelation order. -/
def prefixAt {n : ℕ} (t : Fin n) (x : Cube n) : Cube n :=
  x.filter fun i => i < t

/-- Mass of a specific prefix. -/
noncomputable def prefixMass {n : ℕ} (mu : Cube n → ℝ) (t : Fin n) (pre : Cube n) : ℝ :=
  eventMass mu (fun y => prefixAt t y = prefixAt t pre)

/-- Conditional probability `Pr[X_t = 1 | X_{<t}]`.
Returns 0 if the prefix has 0 mass. -/
noncomputable def condProbOne {n : ℕ} (mu : Cube n → ℝ) (t : Fin n) (x : Cube n) : ℝ :=
  if prefixMass mu t x = 0 then 0 else
  eventMass mu (fun y => prefixAt t y = prefixAt t x ∧ t ∈ y) / prefixMass mu t x

lemma condProbOne_depends_only_on_prefix {n : ℕ} (mu : Cube n → ℝ) (t : Fin n) (x y : Cube n)
    (h_pref : prefixAt t x = prefixAt t y) :
    condProbOne mu t x = condProbOne mu t y := by
  unfold condProbOne
  have h_prefMass : prefixMass mu t x = prefixMass mu t y := by
    unfold prefixMass
    congr 1
    ext z
    rw [h_pref]
  have h_eventMass : eventMass mu (fun z => prefixAt t z = prefixAt t x ∧ t ∈ z) = eventMass mu (fun z => prefixAt t z = prefixAt t y ∧ t ∈ z) := by
    congr 1
    ext z
    rw [h_pref]
  rw [h_prefMass, h_eventMass]

lemma condProbOne_nonneg {n : ℕ} (mu : Cube n → ℝ) (hmu : IsLaw mu)
    (t : Fin n) (x : Cube n) :
    0 ≤ condProbOne mu t x := by
  unfold condProbOne
  split_ifs with hzero
  · exact le_rfl
  · apply div_nonneg
    · unfold eventMass
      exact Finset.sum_nonneg fun y _ => by
        split_ifs
        · exact hmu.1 y
        · exact le_rfl
    · unfold prefixMass eventMass
      exact Finset.sum_nonneg fun y _ => by
        split_ifs
        · exact hmu.1 y
        · exact le_rfl

lemma condProbOne_le_one {n : ℕ} (mu : Cube n → ℝ) (hmu : IsLaw mu)
    (t : Fin n) (x : Cube n) :
    condProbOne mu t x ≤ 1 := by
  unfold condProbOne
  split_ifs with hzero
  · exact zero_le_one
  · have hprefix_nonneg : 0 ≤ prefixMass mu t x := by
      unfold prefixMass eventMass
      exact Finset.sum_nonneg fun y _ => by
        split_ifs
        · exact hmu.1 y
        · exact le_rfl
    have hprefix_pos : 0 < prefixMass mu t x :=
      lt_of_le_of_ne hprefix_nonneg (Ne.symm hzero)
    rw [div_le_one hprefix_pos]
    unfold prefixMass eventMass
    apply Finset.sum_le_sum
    intro y _
    by_cases hpref : prefixAt t y = prefixAt t x
    · by_cases hbit : t ∈ y
      · simp [hpref, hbit]
      · simp only [hpref, true_and, hbit, if_false, if_true]
        exact hmu.1 y
    · simp [hpref]

noncomputable def stepEntropy {n : ℕ} (mu : Cube n → ℝ) (t : Fin n) : ℝ :=
  ∑ x, mu x * Hb (condProbOne mu t x)

lemma stepEntropy_nonneg {n : ℕ} (mu : Cube n → ℝ) (hmu : IsLaw mu) (t : Fin n) :
    0 ≤ stepEntropy mu t := by
  unfold stepEntropy
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg (hmu.1 x)
    (Real.binEntropy_nonneg (condProbOne_nonneg mu hmu t x)
      (condProbOne_le_one mu hmu t x))

lemma stepEntropy_le_log2 {n : ℕ} (mu : Cube n → ℝ) (hmu : IsLaw mu) (t : Fin n) :
    stepEntropy mu t ≤ Real.log 2 := by
  unfold stepEntropy
  calc
    (∑ x, mu x * Hb (condProbOne mu t x)) ≤
        ∑ x, mu x * Real.log 2 := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left Real.binEntropy_le_log_two (hmu.1 x)
    _ = Real.log 2 := by rw [← Finset.sum_mul, hmu.2, one_mul]

/-- The first `k` coordinates of a cube point.  We use a natural-number cutoff
so that the entropy chain rule can telescope from `k = 0` to `k = n`. -/
def prefixNat {n : ℕ} (k : ℕ) (x : Cube n) : Cube n :=
  x.filter fun i => i.1 < k

lemma prefixNat_at {n : ℕ} (t : Fin n) (x : Cube n) :
    prefixNat t.1 x = prefixAt t x := by
  rfl

lemma prefixNat_succ {n k : ℕ} (hk : k < n) (x : Cube n) :
    prefixNat (k + 1) x =
      if (⟨k, hk⟩ : Fin n) ∈ x then
        insert ⟨k, hk⟩ (prefixNat k x)
      else prefixNat k x := by
  classical
  by_cases hx : (⟨k, hk⟩ : Fin n) ∈ x
  · rw [if_pos hx]
    ext i
    simp only [prefixNat, Finset.mem_filter, Finset.mem_insert]
    by_cases hit : i = ⟨k, hk⟩
    · subst i
      simp [hx]
    · have hval : i.1 ≠ k := fun h => hit (Fin.ext h)
      simp only [hit, false_or]
      constructor
      · rintro ⟨hix, hi⟩
        exact ⟨hix, by omega⟩
      · rintro ⟨hix, hi⟩
        exact ⟨hix, by omega⟩
  · rw [if_neg hx]
    ext i
    simp only [prefixNat, Finset.mem_filter]
    constructor
    · rintro ⟨hix, hi⟩
      have hval : i.1 ≠ k := by
        intro h
        apply hx
        have hit : i = (⟨k, hk⟩ : Fin n) := Fin.ext (by simpa using h)
        simpa [hit] using hix
      exact ⟨hix, by omega⟩
    · rintro ⟨hix, hi⟩
      exact ⟨hix, by omega⟩

/-- Canonical values of a length-`k` prefix. -/
def prefixSupport {n : ℕ} (k : ℕ) : Finset (Cube n) :=
  Finset.univ.filter fun c => ∀ i ∈ c, i.1 < k

/-- The marginal mass of a canonical length-`k` prefix. -/
noncomputable def prefixMarginal {n : ℕ} (mu : Cube n → ℝ) (k : ℕ)
    (c : Cube n) : ℝ :=
  eventMass mu fun x => prefixNat k x = c

/-- Entropy of the first `k` coordinates, represented on canonical prefixes. -/
noncomputable def prefixEntropy {n : ℕ} (mu : Cube n → ℝ) (k : ℕ) : ℝ :=
  ∑ c ∈ prefixSupport k, Real.negMulLog (prefixMarginal mu k c)

lemma prefixNat_zero {n : ℕ} (x : Cube n) : prefixNat 0 x = ∅ := by
  ext i
  simp [prefixNat]

lemma prefixNat_dim {n : ℕ} (x : Cube n) : prefixNat n x = x := by
  ext i
  simp [prefixNat]

lemma prefixSupport_zero {n : ℕ} : prefixSupport (n := n) 0 = {∅} := by
  ext c
  simp only [prefixSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · intro h
    apply Finset.ext
    intro i
    constructor
    · intro hi
      exact (Nat.not_lt_zero _ (h i hi)).elim
    · intro hi
      simp at hi
  · rintro rfl i hi
    simp at hi

lemma prefixSupport_dim {n : ℕ} : prefixSupport (n := n) n = Finset.univ := by
  ext c
  simp only [prefixSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun _ => trivial, fun _ i _ => i.isLt⟩

lemma prefixMarginal_dim {n : ℕ} (mu : Cube n → ℝ) (c : Cube n) :
    prefixMarginal mu n c = mu c := by
  unfold prefixMarginal eventMass
  simp_rw [prefixNat_dim]
  simp

lemma prefixMarginal_eq_zero_of_not_mem_prefixSupport
    {n k : ℕ} (nu : Cube n → ℝ) {c : Cube n}
    (hc : c ∉ prefixSupport k) :
    prefixMarginal nu k c = 0 := by
  unfold prefixMarginal eventMass
  apply Finset.sum_eq_zero
  intro x _
  split_ifs with h
  · exfalso
    apply hc
    unfold prefixSupport
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hic
    rw [← h] at hic
    unfold prefixNat at hic
    simp at hic
    exact hic.2
  · rfl

lemma prefixEntropy_zero {n : ℕ} (mu : Cube n → ℝ) (hmu : IsLaw mu) :
    prefixEntropy mu 0 = 0 := by
  rw [prefixEntropy, prefixSupport_zero]
  simp [prefixMarginal, eventMass, prefixNat_zero, hmu.2]

lemma prefixEntropy_dim {n : ℕ} (mu : Cube n → ℝ) :
    prefixEntropy mu n = entropy mu := by
  rw [prefixEntropy, prefixSupport_dim]
  simp_rw [prefixMarginal_dim]
  rfl

lemma prefixSupport_succ_absent {n k : ℕ} (hk : k < n) :
    (prefixSupport (n := n) (k + 1)).filter
        (fun c => (⟨k, hk⟩ : Fin n) ∉ c) =
      prefixSupport k := by
  classical
  ext c
  simp only [prefixSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hc, hnot⟩ i hi
    have hlt := hc i hi
    have hne : i.1 ≠ k := by
      intro h
      apply hnot
      have hit : i = (⟨k, hk⟩ : Fin n) := Fin.ext (by simpa using h)
      simpa [hit] using hi
    omega
  · intro hc
    constructor
    · intro i hi
      exact Nat.lt_succ_of_lt (hc i hi)
    · intro ht
      exact (Nat.lt_irrefl k (hc ⟨k, hk⟩ ht)).elim

lemma prefixSupport_succ_present {n k : ℕ} (hk : k < n) :
    (prefixSupport (n := n) (k + 1)).filter
        (fun c => (⟨k, hk⟩ : Fin n) ∈ c) =
      (prefixSupport k).image (fun c => insert (⟨k, hk⟩ : Fin n) c) := by
  classical
  let t : Fin n := ⟨k, hk⟩
  ext c
  simp only [prefixSupport, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨hc, htc⟩
    refine ⟨c.erase t, ?_, ?_⟩
    · intro i hi
      have hic : i ∈ c := (Finset.mem_erase.mp hi).2
      have hlt := hc i hic
      have hne : i.1 ≠ k := by
        intro h
        have hit : i = t := Fin.ext (by simpa [t] using h)
        exact (Finset.mem_erase.mp hi).1 hit
      omega
    · exact Finset.insert_erase htc
  · rintro ⟨d, hd, rfl⟩
    constructor
    · intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · simp
      · exact Nat.lt_succ_of_lt (hd i hi)
    · exact Finset.mem_insert_self _ _

lemma prefixNat_eq_self_of_mem_support {n k : ℕ} {c : Cube n}
    (hc : c ∈ prefixSupport k) : prefixNat k c = c := by
  rw [prefixSupport, Finset.mem_filter] at hc
  ext i
  simp only [prefixNat, Finset.mem_filter]
  exact ⟨fun h => h.1, fun h => ⟨h, hc.2 i h⟩⟩

lemma cutoff_not_mem_prefixNat {n k : ℕ} (hk : k < n) (x : Cube n) :
    (⟨k, hk⟩ : Fin n) ∉ prefixNat k x := by
  simp [prefixNat]

lemma prefixMarginal_succ_absent {n k : ℕ} (mu : Cube n → ℝ)
    (hk : k < n) {c : Cube n} (hc : c ∈ prefixSupport k) :
    prefixMarginal mu (k + 1) c =
      eventMass mu (fun x => prefixNat k x = c ∧ (⟨k, hk⟩ : Fin n) ∉ x) := by
  have htc : (⟨k, hk⟩ : Fin n) ∉ c := by
    rw [prefixSupport, Finset.mem_filter] at hc
    intro ht
    exact (Nat.lt_irrefl k (by simpa using hc.2 ⟨k, hk⟩ ht)).elim
  unfold prefixMarginal eventMass
  apply Finset.sum_congr rfl
  intro x _
  dsimp only
  rw [prefixNat_succ hk x]
  by_cases hx : (⟨k, hk⟩ : Fin n) ∈ x
  · simp only [hx, if_pos, not_true_eq_false, and_false, if_false]
    apply if_neg
    intro heq
    apply htc
    rw [← heq]
    exact Finset.mem_insert_self _ _
  · simp [hx]

lemma prefixMarginal_succ_present {n k : ℕ} (mu : Cube n → ℝ)
    (hk : k < n) {c : Cube n} (hc : c ∈ prefixSupport k) :
    prefixMarginal mu (k + 1) (insert (⟨k, hk⟩ : Fin n) c) =
      eventMass mu (fun x => prefixNat k x = c ∧ (⟨k, hk⟩ : Fin n) ∈ x) := by
  have htc : (⟨k, hk⟩ : Fin n) ∉ c := by
    rw [prefixSupport, Finset.mem_filter] at hc
    intro ht
    exact (Nat.lt_irrefl k (by simpa using hc.2 ⟨k, hk⟩ ht)).elim
  unfold prefixMarginal eventMass
  apply Finset.sum_congr rfl
  intro x _
  dsimp only
  rw [prefixNat_succ hk x]
  by_cases hx : (⟨k, hk⟩ : Fin n) ∈ x
  · simp only [hx, if_pos, and_true]
    have htx : (⟨k, hk⟩ : Fin n) ∉ prefixNat k x :=
      cutoff_not_mem_prefixNat hk x
    have hinj : insert (⟨k, hk⟩ : Fin n) (prefixNat k x) =
          insert (⟨k, hk⟩ : Fin n) c ↔ prefixNat k x = c := by
      constructor
      · intro h
        have he := congrArg (fun s : Cube n => s.erase (⟨k, hk⟩ : Fin n)) h
        simpa [Finset.erase_insert htx, Finset.erase_insert htc] using he
      · exact congrArg _
    simp only [hinj]
  · simp only [hx, and_false, if_false]
    apply if_neg
    intro heq
    have hmem : (⟨k, hk⟩ : Fin n) ∈ prefixNat k x := by
      rw [heq]
      exact Finset.mem_insert_self _ _
    exact cutoff_not_mem_prefixNat hk x hmem

lemma prefixMarginal_split {n k : ℕ} (mu : Cube n → ℝ)
    (hk : k < n) (c : Cube n) :
    prefixMarginal mu k c =
      eventMass mu (fun x => prefixNat k x = c ∧ (⟨k, hk⟩ : Fin n) ∈ x) +
      eventMass mu (fun x => prefixNat k x = c ∧ (⟨k, hk⟩ : Fin n) ∉ x) := by
  unfold prefixMarginal eventMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hp : prefixNat k x = c
  · by_cases ht : (⟨k, hk⟩ : Fin n) ∈ x <;> simp [hp, ht]
  · simp [hp]

lemma eventMass_nonneg_of_isLaw {n : ℕ} {mu : Cube n → ℝ}
    (hmu : IsLaw mu) (E : Cube n → Prop) : 0 ≤ eventMass mu E := by
  unfold eventMass
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact hmu.1 x
  · exact le_rfl

lemma prefixEntropy_succ_as_split {n k : ℕ} (mu : Cube n → ℝ)
    (hk : k < n) :
    prefixEntropy mu (k + 1) =
      ∑ c ∈ prefixSupport k,
        (Real.negMulLog
            (eventMass mu (fun x => prefixNat k x = c ∧
              (⟨k, hk⟩ : Fin n) ∈ x)) +
          Real.negMulLog
            (eventMass mu (fun x => prefixNat k x = c ∧
              (⟨k, hk⟩ : Fin n) ∉ x))) := by
  classical
  let t : Fin n := ⟨k, hk⟩
  let f : Cube n → ℝ := fun c => Real.negMulLog (prefixMarginal mu (k + 1) c)
  have hinj : Set.InjOn (fun c : Cube n => insert t c)
      (↑(prefixSupport (n := n) k) : Set (Cube n)) := by
    intro a ha b hb hab
    have hta : t ∉ a := by
      change a ∈ prefixSupport (n := n) k at ha
      rw [prefixSupport, Finset.mem_filter] at ha
      intro ht
      exact (Nat.lt_irrefl k (by simpa [t] using ha.2 t ht)).elim
    have htb : t ∉ b := by
      change b ∈ prefixSupport (n := n) k at hb
      rw [prefixSupport, Finset.mem_filter] at hb
      intro ht
      exact (Nat.lt_irrefl k (by simpa [t] using hb.2 t ht)).elim
    have he := congrArg (fun s : Cube n => s.erase t) hab
    simpa [Finset.erase_insert hta, Finset.erase_insert htb] using he
  have hpart := Finset.sum_filter_add_sum_filter_not
    (prefixSupport (n := n) (k + 1)) (fun c => t ∈ c) f
  rw [prefixEntropy]
  rw [← hpart]
  rw [show (prefixSupport (n := n) (k + 1)).filter (fun c => t ∈ c) =
      (prefixSupport k).image (fun c => insert t c) by
        simpa [t] using prefixSupport_succ_present (n := n) hk]
  rw [Finset.sum_image hinj]
  rw [show (prefixSupport (n := n) (k + 1)).filter (fun c => t ∉ c) =
      prefixSupport k by simpa [t] using prefixSupport_succ_absent (n := n) hk]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  dsimp [f]
  rw [prefixMarginal_succ_present mu hk hc,
    prefixMarginal_succ_absent mu hk hc]

lemma condProbOne_eq_prefix_ratio {n k : ℕ} (mu : Cube n → ℝ)
    (hk : k < n) {c : Cube n} (hc : c ∈ prefixSupport k) :
    condProbOne mu (⟨k, hk⟩ : Fin n) c =
      eventMass mu (fun x => prefixNat k x = c ∧ (⟨k, hk⟩ : Fin n) ∈ x) /
        prefixMarginal mu k c := by
  have hfixed : prefixAt (⟨k, hk⟩ : Fin n) c = c := by
    rw [← prefixNat_at, prefixNat_eq_self_of_mem_support hc]
  unfold condProbOne prefixMass prefixMarginal
  rw [hfixed]
  have hpref : (fun y : Cube n => prefixAt (⟨k, hk⟩ : Fin n) y = c) =
      (fun y => prefixNat k y = c) := by
    funext y
    rw [show prefixAt (⟨k, hk⟩ : Fin n) y = prefixNat k y from
      (prefixNat_at (⟨k, hk⟩ : Fin n) y).symm]
  have hpref_one :
      (fun y : Cube n => prefixAt (⟨k, hk⟩ : Fin n) y = c ∧
        (⟨k, hk⟩ : Fin n) ∈ y) =
      (fun y => prefixNat k y = c ∧ (⟨k, hk⟩ : Fin n) ∈ y) := by
    funext y
    rw [show prefixAt (⟨k, hk⟩ : Fin n) y = prefixNat k y from
      (prefixNat_at (⟨k, hk⟩ : Fin n) y).symm]
  rw [hpref, hpref_one]
  by_cases hzero : eventMass mu (fun y => prefixNat k y = c) = 0
  · simp [hzero]
  · simp [hzero]

lemma prefixMarginal_eq_sum_filter {n k : ℕ} (mu : Cube n → ℝ) (c : Cube n) :
    prefixMarginal mu k c =
      ∑ x ∈ Finset.univ.filter (fun x => prefixNat k x = c), mu x := by
  unfold prefixMarginal eventMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : prefixNat k x = c <;> simp [h]

lemma stepEntropy_eq_prefix_sum {n k : ℕ} (mu : Cube n → ℝ)
    (hk : k < n) :
    stepEntropy mu (⟨k, hk⟩ : Fin n) =
      ∑ c ∈ prefixSupport k,
        prefixMarginal mu k c *
          Hb (eventMass mu (fun x => prefixNat k x = c ∧
            (⟨k, hk⟩ : Fin n) ∈ x) / prefixMarginal mu k c) := by
  classical
  unfold stepEntropy
  rw [← Finset.sum_fiberwise Finset.univ (prefixNat k)
    (fun x => mu x * Hb (condProbOne mu (⟨k, hk⟩ : Fin n) x))]
  have hrestrict :
      (∑ c ∈ prefixSupport k,
          ∑ x ∈ Finset.univ.filter (fun x => prefixNat k x = c),
            mu x * Hb (condProbOne mu (⟨k, hk⟩ : Fin n) x)) =
        ∑ c : Cube n,
          ∑ x ∈ Finset.univ.filter (fun x => prefixNat k x = c),
            mu x * Hb (condProbOne mu (⟨k, hk⟩ : Fin n) x) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro c _ hc
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_filter] at hx
    exfalso
    apply hc
    rw [prefixSupport, Finset.mem_filter]
    refine ⟨Finset.mem_univ c, ?_⟩
    intro i hi
    have hip : i ∈ prefixNat k x := by simpa [hx.2] using hi
    exact (Finset.mem_filter.mp hip).2
  rw [← hrestrict]
  apply Finset.sum_congr rfl
  intro c hc
  have hfixed := prefixNat_eq_self_of_mem_support hc
  have hratio := condProbOne_eq_prefix_ratio mu hk hc
  have hconst : ∀ x ∈ Finset.univ.filter (fun x => prefixNat k x = c),
      condProbOne mu (⟨k, hk⟩ : Fin n) x =
        eventMass mu (fun y => prefixNat k y = c ∧ (⟨k, hk⟩ : Fin n) ∈ y) /
          prefixMarginal mu k c := by
    intro x hx
    rw [Finset.mem_filter] at hx
    have hpref : prefixAt (⟨k, hk⟩ : Fin n) x =
        prefixAt (⟨k, hk⟩ : Fin n) c := by
      rw [← prefixNat_at, ← prefixNat_at, hx.2, hfixed]
    rw [condProbOne_depends_only_on_prefix mu _ x c hpref, hratio]
  rw [show
      (∑ x ∈ Finset.univ.filter (fun x => prefixNat k x = c),
          mu x * Hb (condProbOne mu (⟨k, hk⟩ : Fin n) x)) =
        ∑ x ∈ Finset.univ.filter (fun x => prefixNat k x = c),
          mu x * Hb
            (eventMass mu (fun y => prefixNat k y = c ∧
              (⟨k, hk⟩ : Fin n) ∈ y) / prefixMarginal mu k c) by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hconst x hx]]
  rw [← Finset.sum_mul]
  rw [← prefixMarginal_eq_sum_filter (k := k) mu c]

lemma negMulLog_split {A B M : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsum : A + B = M) :
    Real.negMulLog A + Real.negMulLog B =
      Real.negMulLog M + M * Hb (A / M) := by
  by_cases hM : M = 0
  · have hAz : A = 0 := by nlinarith
    have hBz : B = 0 := by nlinarith
    simp [hM, hAz, hBz, Hb]
  · have hAeq : M * (A / M) = A := by field_simp
    have hBeq : M * (1 - A / M) = B := by
      field_simp
      linarith
    calc
      Real.negMulLog A + Real.negMulLog B =
          Real.negMulLog (M * (A / M)) +
            Real.negMulLog (M * (1 - A / M)) := by rw [hAeq, hBeq]
      _ = Real.negMulLog M + M * Hb (A / M) := by
        rw [Real.negMulLog_mul, Real.negMulLog_mul, Hb,
          Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
        ring

lemma prefixEntropy_succ {n k : ℕ} (mu : Cube n → ℝ) (hmu : IsLaw mu)
    (hk : k < n) :
    prefixEntropy mu (k + 1) =
      prefixEntropy mu k + stepEntropy mu (⟨k, hk⟩ : Fin n) := by
  rw [prefixEntropy_succ_as_split mu hk, stepEntropy_eq_prefix_sum mu hk]
  unfold prefixEntropy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  let A := eventMass mu (fun x => prefixNat k x = c ∧
    (⟨k, hk⟩ : Fin n) ∈ x)
  let B := eventMass mu (fun x => prefixNat k x = c ∧
    (⟨k, hk⟩ : Fin n) ∉ x)
  let M := prefixMarginal mu k c
  have hA : 0 ≤ A := eventMass_nonneg_of_isLaw hmu _
  have hB : 0 ≤ B := eventMass_nonneg_of_isLaw hmu _
  have hsum : A + B = M := by
    dsimp [A, B, M]
    exact (prefixMarginal_split mu hk c).symm
  exact negMulLog_split hA hB hsum

lemma entropy_eq_sum_stepEntropy {n : ℕ} (mu : Cube n → ℝ) (hmu : IsLaw mu) :
    entropy mu = ∑ t, stepEntropy mu t := by
  rw [Finset.sum_fin_eq_sum_range]
  calc
    entropy mu = prefixEntropy mu n - prefixEntropy mu 0 := by
      rw [prefixEntropy_dim, prefixEntropy_zero mu hmu]
      ring
    _ = ∑ k ∈ Finset.range n,
          (prefixEntropy mu (k + 1) - prefixEntropy mu k) :=
      (Finset.sum_range_sub (prefixEntropy mu) n).symm
    _ = ∑ k ∈ Finset.range n,
          if hk : k < n then stepEntropy mu (⟨k, hk⟩ : Fin n) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk_mem
      have hk : k < n := Finset.mem_range.mp hk_mem
      rw [dif_pos hk, prefixEntropy_succ mu hmu hk]
      ring

lemma sum_stepEntropy_eq_rate {n : ℕ} (mu : Cube n → ℝ) (hmu : IsLaw mu) :
    ∑ t, stepEntropy mu t = (n : ℝ) * entropyRate n mu := by
  rw [← entropy_eq_sum_stepEntropy mu hmu]
  unfold entropyRate
  by_cases hn : n = 0
  · subst n
    have hmass : mu default = 1 := by simpa using hmu.2
    simp [entropy, hmass]
  · field_simp [Nat.cast_ne_zero.mpr hn]

lemma sum_mglCurve_stepEntropy_ge
    {tau : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
    {n : ℕ} (hn : 1 ≤ n) (mu : Cube n → ℝ) (hmu : IsLaw mu) :
    (n : ℝ) * mglCurve tau (entropyRate n mu) ≤
      ∑ t, mglCurve tau (stepEntropy mu t) := by
  have h_conv := (mglCurve_strictConvex ht0 ht1).convexOn
  have h_n : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by linarith)
  have hn_pos : (n : ℝ) ≠ 0 := ne_of_gt h_n
  have h_inv_n : 0 < (1 / (n : ℝ)) := one_div_pos.mpr h_n
  have h_weights_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ (1 / (n : ℝ)) := fun _ _ => h_inv_n.le
  have h_weights_sum : ∑ i : Fin n, (1 / (n : ℝ)) = 1 := by
    simp
    exact mul_inv_cancel₀ hn_pos
  have h_mem : ∀ i ∈ (Finset.univ : Finset (Fin n)), stepEntropy mu i ∈ Set.Icc (0 : ℝ) (Real.log 2) := by
    intro i _
    exact ⟨stepEntropy_nonneg mu hmu i, stepEntropy_le_log2 mu hmu i⟩
  have h_jensen := h_conv.map_sum_le h_weights_nonneg h_weights_sum h_mem
  have h_rate : entropyRate n mu = ∑ i : Fin n, (1 / (n : ℝ)) * stepEntropy mu i := by
    have h_sum := sum_stepEntropy_eq_rate mu hmu
    have heq : ∑ t, stepEntropy mu t = (n : ℝ) * ∑ i : Fin n, (1 / (n : ℝ)) * stepEntropy mu i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      calc
        stepEntropy mu i = 1 * stepEntropy mu i := by ring
        _ = ((n : ℝ) * (1 / (n : ℝ))) * stepEntropy mu i := by rw [mul_one_div_cancel hn_pos]
        _ = (n : ℝ) * ((1 / (n : ℝ)) * stepEntropy mu i) := by ring
    rw [heq] at h_sum
    exact (mul_left_cancel₀ hn_pos h_sum).symm
  rw [h_rate]
  have h_factor : (n : ℝ) * mglCurve tau (∑ i : Fin n, (1 / (n : ℝ)) * stepEntropy mu i) ≤
    (n : ℝ) * ∑ i : Fin n, (1 / (n : ℝ)) * mglCurve tau (stepEntropy mu i) := by
    apply mul_le_mul_of_nonneg_left h_jensen h_n.le
  have h_simplify : (n : ℝ) * ∑ i : Fin n, (1 / (n : ℝ)) * mglCurve tau (stepEntropy mu i) =
    ∑ t, mglCurve tau (stepEntropy mu t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      (n : ℝ) * ((1 / (n : ℝ)) * mglCurve tau (stepEntropy mu i)) =
          ((n : ℝ) * (1 / (n : ℝ))) * mglCurve tau (stepEntropy mu i) := by ring
      _ = 1 * mglCurve tau (stepEntropy mu i) := by
        rw [mul_one_div_cancel hn_pos]
      _ = mglCurve tau (stepEntropy mu i) := by ring
  exact h_factor.trans_eq h_simplify

lemma mglCurve_Hb_eq_all {tau p : ℝ} (ht0 : 0 < tau) (ht1 : tau < 1 / 2)
  (hp : p ∈ Set.Icc (0 : ℝ) 1) :
  mglCurve tau (Hb p) = Hb (tau + (1 - 2*tau)*p) := by
  have _ := ht0
  have _ := ht1
  rcases le_or_gt p (1/2) with h1 | h1
  · have h_inv : hbInv (Hb p) = p := by
      have hp_mem : p ∈ Icc (0 : ℝ) 2⁻¹ := by
        convert (⟨hp.1, h1⟩ : p ∈ Icc (0 : ℝ) (1/2)) using 1; norm_num
      have hHb_mem : Hb p ∈ Icc (0 : ℝ) (Real.log 2) := by
        constructor
        · exact Real.binEntropy_nonneg hp.1 hp.2
        · exact Real.binEntropy_le_log_two
      have h_spec := hbInv_spec hHb_mem
      have hh1 : hbInv (Hb p) ∈ Icc (0:ℝ) 2⁻¹ := by
        convert h_spec.1 using 1; norm_num
      apply Real.binEntropy_strictMonoOn.injOn hh1 hp_mem h_spec.2
    unfold mglCurve
    rw [h_inv]
  · have heq_hb : Hb (1 - p) = Hb p := Real.binEntropy_one_sub p
    have h_inv : hbInv (Hb p) = 1 - p := by
      have hp_mem : 1 - p ∈ Icc (0 : ℝ) 2⁻¹ := by
        constructor
        · linarith [hp.2]
        · linarith [h1]
      have hHb_mem : Hb p ∈ Icc (0 : ℝ) (Real.log 2) := by
        constructor
        · exact Real.binEntropy_nonneg hp.1 hp.2
        · exact Real.binEntropy_le_log_two
      have h_spec := hbInv_spec hHb_mem
      have hh1 : hbInv (Hb p) ∈ Icc (0:ℝ) 2⁻¹ := by
        convert h_spec.1 using 1; norm_num
      have h_spec2 : Real.binEntropy (hbInv (Hb p)) = Real.binEntropy (1 - p) := by
        change Hb (hbInv (Hb p)) = Hb (1 - p)
        rw [heq_hb]
        exact h_spec.2
      apply Real.binEntropy_strictMonoOn.injOn hh1 hp_mem h_spec2
    unfold mglCurve
    rw [h_inv]
    have h_hb : Hb (tau + (1 - 2 * tau) * (1 - p)) = Hb (tau + (1 - 2 * tau) * p) := by
      have : tau + (1 - 2 * tau) * (1 - p) = 1 - (tau + (1 - 2 * tau) * p) := by ring
      rw [this]
      exact Real.binEntropy_one_sub _
    rw [h_hb]

/-- Scaled finite Jensen inequality for binary entropy.  This form permits a
zero total mass, which is the case needed on zero-mass conditioning fibers in
the conditional-noise argument below. -/
lemma Hb_weighted_average_ge
    {ι : Type*} (s : Finset ι) (w p : ι → ℝ) {M : ℝ}
    (hw : ∀ i ∈ s, 0 ≤ w i) (hM : 0 ≤ M)
    (hwsum : ∑ i ∈ s, w i = M)
    (hp : ∀ i ∈ s, p i ∈ Set.Icc (0 : ℝ) 1) :
    ∑ i ∈ s, w i * Hb (p i) ≤
      M * Hb ((∑ i ∈ s, w i * p i) / M) := by
  rcases hM.eq_or_lt with rfl | hM
  · have hwzero : ∀ i ∈ s, w i = 0 := by
      intro i hi
      have hle : w i ≤ ∑ j ∈ s, w j :=
        Finset.single_le_sum (fun j hj => hw j hj) hi
      rw [hwsum] at hle
      exact le_antisymm hle (hw i hi)
    have hlhs : ∑ i ∈ s, w i * Hb (p i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hwzero i hi, zero_mul]
    rw [hlhs, zero_mul]
  have hnorm_nonneg : ∀ i ∈ s, 0 ≤ w i / M := by
    intro i hi
    exact div_nonneg (hw i hi) hM.le
  have hnorm_sum : ∑ i ∈ s, w i / M = 1 := by
    rw [← Finset.sum_div, hwsum, div_self (ne_of_gt hM)]
  have hj := Real.strictConcave_binEntropy.concaveOn.le_map_sum
    hnorm_nonneg hnorm_sum hp
  simp only [smul_eq_mul] at hj
  change (∑ i ∈ s, w i / M * Hb (p i)) ≤
    Hb (∑ i ∈ s, w i / M * p i) at hj
  have hleft : (∑ i ∈ s, w i / M * Hb (p i)) =
      (∑ i ∈ s, w i * Hb (p i)) / M := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  have harg : (∑ i ∈ s, w i / M * p i) =
      (∑ i ∈ s, w i * p i) / M := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  rw [hleft, harg] at hj
  simpa [mul_comm] using (div_le_iff₀ hM).mp hj

/-- The affine bias produced by a BSC with crossover at most `1/2` is again
a probability. -/
lemma noiseBias_mem_Icc {tau p : ℝ} (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1 / 2)
    (hp : p ∈ Icc (0 : ℝ) 1) :
    tau + (1 - 2 * tau) * p ∈ Icc (0 : ℝ) 1 := by
  have ha : 0 ≤ 1 - 2 * tau := by linarith
  constructor
  · exact add_nonneg ht0 (mul_nonneg ha hp.1)
  · have h := mul_le_mul_of_nonneg_left hp.2 ha
    nlinarith

/-- Binary conditional entropy can only increase when a finite conditioning
partition is coarsened.  The matrix `w i k` is the joint mass of a fine state
`i` and a coarse state `k`; the bit bias depends only on the fine state. -/
lemma Hb_mix_over_columns
    {ι κ : Type*} (si : Finset ι) (sk : Finset κ)
    (w : ι → κ → ℝ) (p : ι → ℝ)
    (hw : ∀ i ∈ si, ∀ k ∈ sk, 0 ≤ w i k)
    (hp : ∀ i ∈ si, p i ∈ Icc (0 : ℝ) 1) :
    ∑ i ∈ si, (∑ k ∈ sk, w i k) * Hb (p i) ≤
      ∑ k ∈ sk, (∑ i ∈ si, w i k) *
        Hb ((∑ i ∈ si, w i k * p i) / (∑ i ∈ si, w i k)) := by
  have hcolumn (k : κ) (hk : k ∈ sk) :
      ∑ i ∈ si, w i k * Hb (p i) ≤
        (∑ i ∈ si, w i k) *
          Hb ((∑ i ∈ si, w i k * p i) / (∑ i ∈ si, w i k)) := by
    apply Hb_weighted_average_ge si (fun i => w i k) p
    · intro i hi
      exact hw i hi k hk
    · exact Finset.sum_nonneg fun i hi => hw i hi k hk
    · rfl
    · exact hp
  calc
    ∑ i ∈ si, (∑ k ∈ sk, w i k) * Hb (p i) =
        ∑ k ∈ sk, ∑ i ∈ si, w i k * Hb (p i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
    _ ≤ ∑ k ∈ sk, (∑ i ∈ si, w i k) *
          Hb ((∑ i ∈ si, w i k * p i) / (∑ i ∈ si, w i k)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hcolumn k hk

/-- Taking a prefix marginal commutes with the finite BSC mixture.  This is
the sum-interchange part of the conditional-noise calculation; the remaining
ingredient is the coordinatewise factorization of `noiseKernel`. -/
lemma prefixMarginal_noiseMass {n k : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (c : Cube n) :
    prefixMarginal (noiseMass tau mu) k c =
      ∑ x, mu x * prefixMarginal (fun y => noiseKernel tau x y) k c := by
  unfold prefixMarginal eventMass noiseMass
  simp only
  calc
    (∑ y : Cube n, @ite ℝ (prefixNat k y = c) (Classical.propDecidable _)
        (∑ x : Cube n, mu x * noiseKernel tau x y) 0) =
        ∑ y : Cube n, ∑ x : Cube n,
          if prefixNat k y = c then mu x * noiseKernel tau x y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : prefixNat k y = c <;> simp [h]
    _ = ∑ x : Cube n, ∑ y : Cube n,
          if prefixNat k y = c then mu x * noiseKernel tau x y else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x : Cube n, mu x *
          ∑ y : Cube n, if prefixNat k y = c then noiseKernel tau x y else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : prefixNat k y = c <;> simp [h]

/-- The canonical prefix marginals of a law form a law on the finite prefix
support. -/
lemma sum_prefixMarginal_eq_one {n k : ℕ} (mu : Cube n → ℝ)
    (hmu : IsLaw mu) :
    ∑ c ∈ prefixSupport k, prefixMarginal mu k c = 1 := by
  simp_rw [prefixMarginal_eq_sum_filter]
  have hrestrict :
      (∑ c ∈ prefixSupport k,
          ∑ x ∈ Finset.univ.filter (fun x => prefixNat k x = c), mu x) =
        ∑ c : Cube n,
          ∑ x ∈ Finset.univ.filter (fun x => prefixNat k x = c), mu x := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro c _ hc
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_filter] at hx
    exfalso
    apply hc
    rw [prefixSupport, Finset.mem_filter]
    refine ⟨Finset.mem_univ c, ?_⟩
    intro i hi
    have hip : i ∈ prefixNat k x := by simpa [hx.2] using hi
    exact (Finset.mem_filter.mp hip).2
  rw [hrestrict, Finset.sum_fiberwise, hmu.2]

/-- For a fixed input, the BSC transition kernel is itself a law. -/
lemma noiseKernel_isLaw {n : ℕ} {tau : ℝ} (ht0 : 0 ≤ tau) (ht1 : tau ≤ 1)
    (x : Cube n) : IsLaw (noiseKernel tau x) := by
  let point : Cube n → ℝ := fun z => if z = x then 1 else 0
  have hpoint : IsLaw point := by
    constructor
    · intro z
      dsimp [point]
      split_ifs <;> norm_num
    · dsimp [point]
      simp
  have hnoise := noiseMass_isLaw ht0 ht1 point hpoint
  have heq : noiseMass tau point = noiseKernel tau x := by
    funext y
    unfold noiseMass
    dsimp [point]
    simp
  rwa [heq] at hnoise

private def toggleAt {n : ℕ} (t : Fin n) (y : Cube n) : Cube n :=
  symmDiff {t} y

private lemma toggleAt_involutive {n : ℕ} (t : Fin n) :
    Function.Involutive (toggleAt t) := by
  intro y
  simp [toggleAt, symmDiff_symmDiff_cancel_left]

private lemma prefixNat_toggleAt {n : ℕ} (t : Fin n) (y : Cube n) :
    prefixNat t.1 (toggleAt t y) = prefixNat t.1 y := by
  ext i
  simp only [prefixNat, Finset.mem_filter]
  constructor
  · rintro ⟨hi, hlt⟩
    refine ⟨?_, hlt⟩
    rw [toggleAt, Finset.mem_symmDiff] at hi
    rcases hi with ⟨hit, hiy⟩ | ⟨hiy, hit⟩
    · simp at hit
      subst i
      exact (Nat.lt_irrefl _ hlt).elim
    · exact hiy
  · rintro ⟨hiy, hlt⟩
    refine ⟨?_, hlt⟩
    rw [toggleAt, Finset.mem_symmDiff]
    right
    refine ⟨hiy, ?_⟩
    simp only [Finset.mem_singleton]
    intro hit
    subst i
    exact Nat.lt_irrefl _ hlt

private lemma mem_toggleAt_iff {n : ℕ} (t : Fin n) (y : Cube n) :
    t ∈ toggleAt t y ↔ t ∉ y := by
  simp [toggleAt, Finset.mem_symmDiff]

private lemma toggleAt_eq_insert {n : ℕ} (t : Fin n) (y : Cube n)
    (hy : t ∉ y) : toggleAt t y = insert t y := by
  ext i
  by_cases hit : i = t
  · subst i
    simp [toggleAt, Finset.mem_symmDiff, hy]
  · simp [toggleAt, Finset.mem_symmDiff, hit]

private lemma hDist_insert_of_mem_left {n : ℕ} (x y : Cube n) (t : Fin n)
    (hxt : t ∈ x) (hyt : t ∉ y) :
    hDist x (insert t y) + 1 = hDist x y := by
  have hsd : symmDiff x (insert t y) = (symmDiff x y).erase t := by
    ext i
    by_cases hit : i = t
    · subst i
      simp [Finset.mem_symmDiff, hxt, hyt]
    · simp [Finset.mem_symmDiff, hit]
  have htmem : t ∈ symmDiff x y := by
    simp [Finset.mem_symmDiff, hxt, hyt]
  unfold hDist
  rw [hsd]
  exact Finset.card_erase_add_one htmem

private lemma hDist_insert_of_not_mem_left {n : ℕ} (x y : Cube n) (t : Fin n)
    (hxt : t ∉ x) (hyt : t ∉ y) :
    hDist x (insert t y) = hDist x y + 1 := by
  have hsd : symmDiff x (insert t y) = insert t (symmDiff x y) := by
    ext i
    by_cases hit : i = t
    · subst i
      simp [Finset.mem_symmDiff, hxt, hyt]
    · simp [Finset.mem_symmDiff, hit]
  have htmem : t ∉ symmDiff x y := by
    simp [Finset.mem_symmDiff, hxt, hyt]
  unfold hDist
  rw [hsd, Finset.card_insert_of_notMem htmem]

private lemma hDist_le_dim_entropyChain {n : ℕ} (x y : Cube n) :
    hDist x y ≤ n := by
  simpa [hDist] using Finset.card_le_univ (symmDiff x y)

private lemma noiseKernel_insert_relation_mem {n : ℕ} (tau : ℝ)
    (x y : Cube n) (t : Fin n) (hxt : t ∈ x) (hyt : t ∉ y) :
    tau * noiseKernel tau x (insert t y) =
      (1 - tau) * noiseKernel tau x y := by
  have hd := hDist_insert_of_mem_left x y t hxt hyt
  have hle := hDist_le_dim_entropyChain x y
  have hcomp : n - hDist x (insert t y) = (n - hDist x y) + 1 := by omega
  unfold noiseKernel
  rw [hcomp, ← hd, pow_succ, pow_succ]
  ring

private lemma noiseKernel_insert_relation_not_mem {n : ℕ} (tau : ℝ)
    (x y : Cube n) (t : Fin n) (hxt : t ∉ x) (hyt : t ∉ y) :
    (1 - tau) * noiseKernel tau x (insert t y) =
      tau * noiseKernel tau x y := by
  have hd := hDist_insert_of_not_mem_left x y t hxt hyt
  have hle := hDist_le_dim_entropyChain x (insert t y)
  have hcomp : n - hDist x y = (n - hDist x (insert t y)) + 1 := by omega
  unfold noiseKernel
  rw [hcomp, hd, pow_succ, pow_succ]
  ring

private lemma noiseKernel_prefix_one_balance_mem {n : ℕ} (tau : ℝ)
    (x c : Cube n) (t : Fin n) (hxt : t ∈ x) :
    tau * eventMass (noiseKernel tau x)
        (fun y => prefixNat t.1 y = c ∧ t ∈ y) =
      (1 - tau) * eventMass (noiseKernel tau x)
        (fun y => prefixNat t.1 y = c ∧ t ∉ y) := by
  let e : Cube n ≃ Cube n :=
    { toFun := toggleAt t
      invFun := toggleAt t
      left_inv := toggleAt_involutive t
      right_inv := toggleAt_involutive t }
  unfold eventMass
  rw [Finset.mul_sum, Finset.mul_sum]
  simp_rw [mul_ite, mul_zero]
  have hshift := Equiv.sum_comp e (fun y : Cube n =>
    if prefixNat t.1 y = c ∧ t ∈ y then tau * noiseKernel tau x y else 0)
  rw [← hshift]
  apply Finset.sum_congr rfl
  intro y _
  dsimp [e]
  simp only [prefixNat_toggleAt, mem_toggleAt_iff]
  by_cases hp : prefixNat t.1 y = c
  · by_cases hy : t ∈ y
    · simp [hp, hy]
    · rw [if_pos ⟨hp, hy⟩, if_pos ⟨hp, hy⟩]
      rw [toggleAt_eq_insert t y hy]
      exact noiseKernel_insert_relation_mem tau x y t hxt hy
  · simp [hp]

private lemma noiseKernel_prefix_one_balance_not_mem {n : ℕ} (tau : ℝ)
    (x c : Cube n) (t : Fin n) (hxt : t ∉ x) :
    (1 - tau) * eventMass (noiseKernel tau x)
        (fun y => prefixNat t.1 y = c ∧ t ∈ y) =
      tau * eventMass (noiseKernel tau x)
        (fun y => prefixNat t.1 y = c ∧ t ∉ y) := by
  let e : Cube n ≃ Cube n :=
    { toFun := toggleAt t
      invFun := toggleAt t
      left_inv := toggleAt_involutive t
      right_inv := toggleAt_involutive t }
  unfold eventMass
  rw [Finset.mul_sum, Finset.mul_sum]
  simp_rw [mul_ite, mul_zero]
  have hshift := Equiv.sum_comp e (fun y : Cube n =>
    if prefixNat t.1 y = c ∧ t ∈ y then
      (1 - tau) * noiseKernel tau x y else 0)
  rw [← hshift]
  apply Finset.sum_congr rfl
  intro y _
  dsimp [e]
  simp only [prefixNat_toggleAt, mem_toggleAt_iff]
  by_cases hp : prefixNat t.1 y = c
  · by_cases hy : t ∈ y
    · simp [hp, hy]
    · rw [if_pos ⟨hp, hy⟩, if_pos ⟨hp, hy⟩]
      rw [toggleAt_eq_insert t y hy]
      exact noiseKernel_insert_relation_not_mem tau x y t hxt hy
  · simp [hp]

/-- Under the product BSC, the current output bit is independent of the past
output prefix once the input point is fixed. -/
lemma noiseKernel_prefix_one_factor {n : ℕ} (tau : ℝ)
    (x c : Cube n) (t : Fin n) :
    eventMass (noiseKernel tau x)
        (fun y => prefixNat t.1 y = c ∧ t ∈ y) =
      prefixMarginal (noiseKernel tau x) t.1 c *
        (if t ∈ x then 1 - tau else tau) := by
  let A := eventMass (noiseKernel tau x)
    (fun y => prefixNat t.1 y = c ∧ t ∈ y)
  let B := eventMass (noiseKernel tau x)
    (fun y => prefixNat t.1 y = c ∧ t ∉ y)
  have hsplit := prefixMarginal_split (noiseKernel tau x) t.isLt c
  change prefixMarginal (noiseKernel tau x) t.1 c = A + B at hsplit
  change A = prefixMarginal (noiseKernel tau x) t.1 c *
    (if t ∈ x then 1 - tau else tau)
  by_cases hxt : t ∈ x
  · rw [if_pos hxt]
    have hbal := noiseKernel_prefix_one_balance_mem tau x c t hxt
    change tau * A = (1 - tau) * B at hbal
    rw [hsplit]
    calc
      A = (1 - tau) * A + tau * A := by ring
      _ = (1 - tau) * A + (1 - tau) * B := by rw [hbal]
      _ = (A + B) * (1 - tau) := by ring
  · rw [if_neg hxt]
    have hbal := noiseKernel_prefix_one_balance_not_mem tau x c t hxt
    change (1 - tau) * A = tau * B at hbal
    rw [hsplit]
    calc
      A = (1 - tau) * A + tau * A := by ring
      _ = tau * B + tau * A := by rw [hbal]
      _ = (A + B) * tau := by ring

private def translateCube {n : ℕ} (d y : Cube n) : Cube n := symmDiff d y

private lemma translateCube_involutive {n : ℕ} (d : Cube n) :
    Function.Involutive (translateCube d) := by
  intro y
  simp [translateCube, symmDiff_symmDiff_cancel_left]

private lemma prefixNat_translate_diff {n k : ℕ} (x x' y : Cube n)
    (hpre : prefixNat k x = prefixNat k x') :
    prefixNat k (translateCube (symmDiff x x') y) = prefixNat k y := by
  ext i
  simp only [prefixNat, Finset.mem_filter]
  constructor
  · rintro ⟨hi, hlt⟩
    refine ⟨?_, hlt⟩
    have hmem : i ∈ x ↔ i ∈ x' := by
      have := congrArg (fun z : Cube n => i ∈ z) hpre
      simpa [prefixNat, hlt] using this
    rw [translateCube, Finset.mem_symmDiff] at hi
    rcases hi with ⟨hid, hiy⟩ | ⟨hiy, hid⟩
    · rw [Finset.mem_symmDiff] at hid
      rcases hid with ⟨hix, hnix'⟩ | ⟨hix', hnix⟩
      · exact (hnix' (hmem.mp hix)).elim
      · exact (hnix (hmem.mpr hix')).elim
    · exact hiy
  · rintro ⟨hiy, hlt⟩
    refine ⟨?_, hlt⟩
    have hmem : i ∈ x ↔ i ∈ x' := by
      have := congrArg (fun z : Cube n => i ∈ z) hpre
      simpa [prefixNat, hlt] using this
    rw [translateCube, Finset.mem_symmDiff]
    right
    refine ⟨hiy, ?_⟩
    rw [Finset.mem_symmDiff]
    rintro (⟨hix, hnix'⟩ | ⟨hix', hnix⟩)
    · exact hnix' (hmem.mp hix)
    · exact hnix (hmem.mpr hix')

private lemma hDist_translate_diff {n : ℕ} (x x' y : Cube n) :
    hDist x' (translateCube (symmDiff x x') y) = hDist x y := by
  unfold hDist translateCube
  congr 1
  simp [symmDiff_left_comm, symmDiff_comm]

private lemma noiseKernel_translate_diff {n : ℕ} (tau : ℝ)
    (x x' y : Cube n) :
    noiseKernel tau x' (translateCube (symmDiff x x') y) =
      noiseKernel tau x y := by
  unfold noiseKernel
  rw [hDist_translate_diff]

/-- The BSC mass of an output-prefix fiber depends on the input only through
the corresponding input prefix. -/
lemma prefixMarginal_noiseKernel_depends_only_on_prefix
    {n k : ℕ} (tau : ℝ) (x x' c : Cube n)
    (hpre : prefixNat k x = prefixNat k x') :
    prefixMarginal (noiseKernel tau x) k c =
      prefixMarginal (noiseKernel tau x') k c := by
  let e : Cube n ≃ Cube n :=
    { toFun := translateCube (symmDiff x x')
      invFun := translateCube (symmDiff x x')
      left_inv := translateCube_involutive _
      right_inv := translateCube_involutive _ }
  unfold prefixMarginal eventMass
  have hshift := Equiv.sum_comp e (fun y : Cube n =>
    @ite ℝ (prefixNat k y = c) (Classical.propDecidable _)
      (noiseKernel tau x' y) 0)
  rw [← hshift]
  apply Finset.sum_congr rfl
  intro y _
  dsimp [e]
  rw [prefixNat_translate_diff x x' y hpre,
    noiseKernel_translate_diff tau x x' y]

private lemma bitFactor_prefix_sum {n k : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (hmu : IsLaw mu) (hk : k < n) (c : Cube n) (hc : c ∈ prefixSupport k) :
    ∑ x ∈ Finset.univ.filter (fun x => prefixNat k x = c),
        mu x * (if (⟨k, hk⟩ : Fin n) ∈ x then 1 - tau else tau) =
      prefixMarginal mu k c *
        (tau + (1 - 2 * tau) * condProbOne mu (⟨k, hk⟩ : Fin n) c) := by
  let t : Fin n := ⟨k, hk⟩
  let A := eventMass mu (fun x => prefixNat k x = c ∧ t ∈ x)
  let B := eventMass mu (fun x => prefixNat k x = c ∧ t ∉ x)
  let M := prefixMarginal mu k c
  have hsplit := prefixMarginal_split mu hk c
  change M = A + B at hsplit
  have hratio := condProbOne_eq_prefix_ratio mu hk hc
  change condProbOne mu t c = A / M at hratio
  have hlhs :
      (∑ x ∈ Finset.univ.filter (fun x => prefixNat k x = c),
          mu x * (if t ∈ x then 1 - tau else tau)) =
        (1 - tau) * A + tau * B := by
    dsimp [A, B]
    unfold eventMass
    simp_rw [Finset.sum_filter]
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hp : prefixNat k x = c
    · by_cases ht : t ∈ x <;> simp [hp, ht] <;> ring
    · simp [hp]
  change (∑ x ∈ Finset.univ.filter (fun x => prefixNat k x = c),
      mu x * (if t ∈ x then 1 - tau else tau)) =
    M * (tau + (1 - 2 * tau) * condProbOne mu t c)
  rw [hlhs, hratio]
  by_cases hM : M = 0
  · have hA : A = 0 := by
      have hA0 : 0 ≤ A := by
        dsimp [A]
        unfold eventMass
        exact Finset.sum_nonneg fun x _ => by
          split_ifs
          · exact hmu.1 x
          · exact le_rfl
      have hB0 : 0 ≤ B := by
        dsimp [B]
        unfold eventMass
        exact Finset.sum_nonneg fun x _ => by
          split_ifs
          · exact hmu.1 x
          · exact le_rfl
      rw [hM] at hsplit
      linarith
    have hB : B = 0 := by rw [hM, hA] at hsplit; linarith
    simp [hM, hA, hB]
  · field_simp
    rw [hsplit]
    ring

/-- Event mass commutes with the finite BSC mixture. -/
lemma eventMass_noiseMass {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (E : Cube n → Prop) :
    eventMass (noiseMass tau mu) E =
      ∑ x, mu x * eventMass (noiseKernel tau x) E := by
  unfold eventMass noiseMass
  calc
    (∑ y : Cube n, @ite ℝ (E y) (Classical.propDecidable _)
        (∑ x : Cube n, mu x * noiseKernel tau x y) 0) =
        ∑ y : Cube n, ∑ x : Cube n,
          if E y then mu x * noiseKernel tau x y else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : E y <;> simp [h]
    _ = ∑ x : Cube n, ∑ y : Cube n,
          if E y then mu x * noiseKernel tau x y else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x : Cube n, mu x *
          ∑ y : Cube n, if E y then noiseKernel tau x y else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      by_cases h : E y <;> simp [h]

private lemma sum_eq_sum_prefixSupport {n k : ℕ} (f : Cube n → ℝ) :
    ∑ x, f x =
      ∑ c ∈ prefixSupport k,
        ∑ x ∈ Finset.univ.filter (fun x => prefixNat k x = c), f x := by
  have hrestrict :
      (∑ c ∈ prefixSupport k,
          ∑ x ∈ Finset.univ.filter (fun x => prefixNat k x = c), f x) =
        ∑ c : Cube n,
          ∑ x ∈ Finset.univ.filter (fun x => prefixNat k x = c), f x := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro c _ hc
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_filter] at hx
    exfalso
    apply hc
    rw [prefixSupport, Finset.mem_filter]
    refine ⟨Finset.mem_univ c, ?_⟩
    intro i hi
    have hip : i ∈ prefixNat k x := by simpa [hx.2] using hi
    exact (Finset.mem_filter.mp hip).2
  rw [hrestrict, Finset.sum_fiberwise]

/-- Joint mass of a noisy prefix and current output bit, expressed as the
posterior mixture of the clean-prefix output biases. -/
lemma noisePrefix_one_mass_eq {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (hmu : IsLaw mu) (t : Fin n) (c : Cube n) :
    (∑ x, mu x * prefixMarginal (noiseKernel tau x) t.1 c *
        (tau + (1 - 2 * tau) * condProbOne mu t x)) =
      eventMass (noiseMass tau mu)
        (fun y => prefixNat t.1 y = c ∧ t ∈ y) := by
  rw [eventMass_noiseMass]
  simp_rw [noiseKernel_prefix_one_factor]
  rw [sum_eq_sum_prefixSupport
      (fun x => mu x * prefixMarginal (noiseKernel tau x) t.1 c *
        (tau + (1 - 2 * tau) * condProbOne mu t x))]
  rw [sum_eq_sum_prefixSupport
      (fun x => mu x *
        (prefixMarginal (noiseKernel tau x) t.1 c *
          (if t ∈ x then 1 - tau else tau)))]
  apply Finset.sum_congr rfl
  intro a ha
  have haa := prefixNat_eq_self_of_mem_support ha
  have hbit := bitFactor_prefix_sum tau mu hmu t.isLt a ha
  change (∑ x ∈ Finset.univ.filter (fun x => prefixNat t.1 x = a),
      mu x * (if t ∈ x then 1 - tau else tau)) =
    prefixMarginal mu t.1 a *
      (tau + (1 - 2 * tau) * condProbOne mu t a) at hbit
  have hleft :
      (∑ x ∈ Finset.univ.filter (fun x => prefixNat t.1 x = a),
        mu x * prefixMarginal (noiseKernel tau x) t.1 c *
          (tau + (1 - 2 * tau) * condProbOne mu t x)) =
      prefixMarginal (noiseKernel tau a) t.1 c *
        (tau + (1 - 2 * tau) * condProbOne mu t a) *
          prefixMarginal mu t.1 a := by
    calc
      _ = ∑ x ∈ Finset.univ.filter (fun x => prefixNat t.1 x = a),
          mu x * (prefixMarginal (noiseKernel tau a) t.1 c *
            (tau + (1 - 2 * tau) * condProbOne mu t a)) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mem_filter] at hx
        have hk := prefixMarginal_noiseKernel_depends_only_on_prefix
          tau x a c (by rw [hx.2, haa])
        have hp : condProbOne mu t x = condProbOne mu t a := by
          apply condProbOne_depends_only_on_prefix
          rw [← prefixNat_at, ← prefixNat_at, hx.2, haa]
        rw [hk, hp]
        ring
      _ = (∑ x ∈ Finset.univ.filter (fun x => prefixNat t.1 x = a), mu x) *
          (prefixMarginal (noiseKernel tau a) t.1 c *
            (tau + (1 - 2 * tau) * condProbOne mu t a)) := by
        rw [Finset.sum_mul]
      _ = _ := by
        rw [← prefixMarginal_eq_sum_filter (k := t.1) mu a]
        ring
  have hright :
      (∑ x ∈ Finset.univ.filter (fun x => prefixNat t.1 x = a),
        mu x * (prefixMarginal (noiseKernel tau x) t.1 c *
          (if t ∈ x then 1 - tau else tau))) =
      prefixMarginal (noiseKernel tau a) t.1 c *
        (prefixMarginal mu t.1 a *
          (tau + (1 - 2 * tau) * condProbOne mu t a)) := by
    rw [← hbit]
    calc
      _ = ∑ x ∈ Finset.univ.filter (fun x => prefixNat t.1 x = a),
          prefixMarginal (noiseKernel tau a) t.1 c *
            (mu x * (if t ∈ x then 1 - tau else tau)) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mem_filter] at hx
        have hk := prefixMarginal_noiseKernel_depends_only_on_prefix
          tau x a c (by rw [hx.2, haa])
        rw [hk]
        ring
      _ = _ := by rw [Finset.mul_sum]
  rw [hleft, hright]
  ring

lemma stepEntropy_noise_ge_condMGL {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (hmu : IsLaw mu) (ht0 : 0 < tau) (ht1 : tau < 1 / 2) (t : Fin n) :
    (∑ x, mu x * Hb (tau + (1 - 2*tau) * condProbOne mu t x)) ≤ stepEntropy (noiseMass tau mu) t := by
  let w : Cube n → Cube n → ℝ := fun x c =>
    mu x * prefixMarginal (noiseKernel tau x) t.1 c
  let p : Cube n → ℝ := fun x =>
    tau + (1 - 2 * tau) * condProbOne mu t x
  have hkernel (x : Cube n) : IsLaw (noiseKernel tau x) :=
    noiseKernel_isLaw ht0.le (by linarith) x
  have hw : ∀ x ∈ (Finset.univ : Finset (Cube n)),
      ∀ c ∈ prefixSupport t.1, 0 ≤ w x c := by
    intro x _ c _
    exact mul_nonneg (hmu.1 x)
      (eventMass_nonneg_of_isLaw (hkernel x) _)
  have hp : ∀ x ∈ (Finset.univ : Finset (Cube n)), p x ∈ Icc (0 : ℝ) 1 := by
    intro x _
    exact noiseBias_mem_Icc ht0.le ht1.le
      ⟨condProbOne_nonneg mu hmu t x, condProbOne_le_one mu hmu t x⟩
  have hmix := Hb_mix_over_columns
    (Finset.univ : Finset (Cube n)) (prefixSupport t.1) w p hw hp
  have hleft :
      (∑ x, (∑ c ∈ prefixSupport t.1, w x c) * Hb (p x)) =
        ∑ x, mu x * Hb (tau + (1 - 2 * tau) * condProbOne mu t x) := by
    apply Finset.sum_congr rfl
    intro x _
    have hsum := sum_prefixMarginal_eq_one (k := t.1)
      (noiseKernel tau x) (hkernel x)
    dsimp [w, p]
    rw [← Finset.mul_sum, hsum, mul_one]
  have hright :
      (∑ c ∈ prefixSupport t.1, (∑ x, w x c) *
        Hb ((∑ x, w x c * p x) / (∑ x, w x c))) =
        stepEntropy (noiseMass tau mu) t := by
    rw [show t = (⟨t.1, t.isLt⟩ : Fin n) from Fin.ext rfl]
    rw [stepEntropy_eq_prefix_sum (noiseMass tau mu) t.isLt]
    apply Finset.sum_congr rfl
    intro c _
    have hden := prefixMarginal_noiseMass (k := t.1) tau mu c
    have hnum := noisePrefix_one_mass_eq tau mu hmu t c
    dsimp [w, p]
    rw [← hden, hnum]
  rw [hleft, hright] at hmix
  exact hmix

-- conditional Mrs.-Gerber
lemma stepEntropy_noise_ge_mgl {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ)
    (hmu : IsLaw mu) (ht0 : 0 < tau) (ht1 : tau < 1 / 2) (t : Fin n) :
    mglCurve tau (stepEntropy mu t) ≤ stepEntropy (noiseMass tau mu) t := by
  have h_conv := (mglCurve_strictConvex ht0 ht1).convexOn
  unfold stepEntropy
  have hsum : ∑ x, mu x = 1 := hmu.2
  have hw : ∀ x ∈ Finset.univ, 0 ≤ mu x := fun x _ => hmu.1 x
  have hp : ∀ x ∈ Finset.univ, Hb (condProbOne mu t x) ∈ Icc (0 : ℝ) (Real.log 2) := by
    intro x _
    constructor
    · exact Real.binEntropy_nonneg (condProbOne_nonneg mu hmu t x) (condProbOne_le_one mu hmu t x)
    · exact Real.binEntropy_le_log_two
  have h_jensen := h_conv.map_sum_le hw hsum hp
  have h_jensen2 : mglCurve tau (∑ x, mu x * Hb (condProbOne mu t x)) ≤ ∑ x, mu x * mglCurve tau (Hb (condProbOne mu t x)) := by
    simpa using h_jensen
  have h_rewrite : ∑ x, mu x * mglCurve tau (Hb (condProbOne mu t x)) =
      ∑ x, mu x * Hb (tau + (1 - 2*tau) * condProbOne mu t x) := by
    apply Finset.sum_congr rfl
    intro x _
    have h_cpo : condProbOne mu t x ∈ Icc (0:ℝ) 1 :=
      ⟨condProbOne_nonneg mu hmu t x, condProbOne_le_one mu hmu t x⟩
    rw [mglCurve_Hb_eq_all ht0 ht1 h_cpo]
  rw [h_rewrite] at h_jensen2
  exact h_jensen2.trans (stepEntropy_noise_ge_condMGL tau mu hmu ht0 ht1 t)

-- The two components of the Mrs. Gerber / Jensen gap:
noncomputable def S_mem {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ) : ℝ :=
  entropy (noiseMass tau mu) - ∑ t, mglCurve tau (stepEntropy mu t)

noncomputable def S_jen {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ) : ℝ :=
  (∑ t, mglCurve tau (stepEntropy mu t)) - (n : ℝ) * mglCurve tau (entropyRate n mu)

lemma S_mem_nonneg {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ) (hmu : IsLaw mu)
    (ht0 : 0 < tau) (ht1 : tau < 1 / 2) : 0 ≤ S_mem tau mu := by
  unfold S_mem
  have ht1_le : tau ≤ 1 := le_of_lt (ht1.trans (by norm_num))
  have h_noise_law := noiseMass_isLaw ht0.le ht1_le mu hmu
  rw [entropy_eq_sum_stepEntropy _ h_noise_law]
  have h_le : ∑ t, mglCurve tau (stepEntropy mu t) ≤ ∑ t, stepEntropy (noiseMass tau mu) t := by
    apply Finset.sum_le_sum
    intro t _
    exact stepEntropy_noise_ge_mgl tau mu hmu ht0 ht1 t
  linarith

lemma S_jen_nonneg {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ) (hmu : IsLaw mu)
    (ht0 : 0 < tau) (ht1 : tau < 1 / 2) (hn : 1 ≤ n) : 0 ≤ S_jen tau mu := by
  unfold S_jen
  have h := sum_mglCurve_stepEntropy_ge ht0 ht1 hn mu hmu
  linarith

lemma slack_split {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ) :
    entropy (noiseMass tau mu) - (n : ℝ) * mglCurve tau (entropyRate n mu) =
      S_jen tau mu + S_mem tau mu := by
  unfold S_jen S_mem
  ring

lemma S_jen_le_delta_n {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ) (delta : ℝ) (hmu : IsLaw mu)
    (ht0 : 0 < tau) (ht1 : tau < 1 / 2) (hn : 1 ≤ n)
    (h_ent : entropy (noiseMass tau mu) ≤ (n : ℝ) * mglCurve tau (entropyRate n mu) + delta * (n : ℝ)) :
    S_jen tau mu ≤ delta * (n : ℝ) := by
  have _ := hn
  have h_split := slack_split tau mu
  have h_mem_nonneg := S_mem_nonneg tau mu hmu ht0 ht1
  linarith

lemma S_mem_le_delta_n {n : ℕ} (tau : ℝ) (mu : Cube n → ℝ) (delta : ℝ) (hmu : IsLaw mu)
    (ht0 : 0 < tau) (ht1 : tau < 1 / 2) (hn : 1 ≤ n)
    (h_ent : entropy (noiseMass tau mu) ≤ (n : ℝ) * mglCurve tau (entropyRate n mu) + delta * (n : ℝ)) :
    S_mem tau mu ≤ delta * (n : ℝ) := by
  have h_split := slack_split tau mu
  have h_jen_nonneg := S_jen_nonneg tau mu hmu ht0 ht1 hn
  linarith

end AverageHarperStability
