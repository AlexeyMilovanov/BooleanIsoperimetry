import Mathlib

-- Disable strict linters for stylistic warnings
set_option linter.style.openClassical false
set_option linter.style.induction false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.style.multiGoal false
set_option linter.style.refine false

open Classical
open scoped BigOperators

-- 1. Boolean Cube definition (vertex as a set of active indices)
abbrev Cube (n : ℕ) := Finset (Fin n)

-- 2. Hamming metric (size of symmetric difference)
noncomputable def hDist {n : ℕ} (x y : Cube n) : ℕ :=
  (symmDiff x y).card

-- 3. r-neighborhood of a set
noncomputable def neighborhood {n : ℕ} (r : ℕ) (A : Finset (Cube n)) : Finset (Cube n) :=
  Finset.univ.filter (fun v => ∃ u ∈ A, hDist u v ≤ r)

@[simp]
lemma mem_neighborhood_iff {n r : ℕ} {A : Finset (Cube n)} {v : Cube n} :
  v ∈ neighborhood r A ↔ ∃ u ∈ A, hDist u v ≤ r := by
  simp [neighborhood]

-- 4. Hamming Ball centered at the origin
noncomputable def hammingBall {n : ℕ} (r : ℕ) : Finset (Cube n) :=
  Finset.univ.filter (fun v => v.card ≤ r)

-- 5. Binary encoding for simplicial ordering
noncomputable def cubeToNat {n : ℕ} (x : Cube n) : ℕ :=
  ∑ i ∈ x, 2 ^ (i : ℕ)

-- 6. Simplicial order definition (Weight first, then lexicographical/binary)
def simplicialLe {n : ℕ} (x y : Cube n) : Prop :=
  x.card < y.card ∨ (x.card = y.card ∧ cubeToNat x ≤ cubeToNat y)

def simplicialLt {n : ℕ} (x y : Cube n) : Prop :=
  simplicialLe x y ∧ ¬simplicialLe y x

-- ==========================================
-- BLOCK 1: INJECTIVITY OF ENCODING
-- ==========================================

lemma sum_pow_two_lt (n : ℕ) : (∑ i ∈ Finset.range n, 2^i) < 2^n := by
  rw [ Nat.geomSum_eq ] <;> norm_num

lemma cubeToNat_inj {n : ℕ} {x y : Cube n} (h : cubeToNat x = cubeToNat y) : x = y := by
  revert x y;
  have h_unique_binary : ∀ {x y : Finset ℕ}, x ⊆ Finset.range n → y ⊆ Finset.range n → (∑ i ∈ x, 2^i) = (∑ i ∈ y, 2^i) → x = y := by
    intros x y hx hy hsum_eq
    have h_binary_eq : (Nat.ofDigits 2 (List.map (fun i => if i ∈ x then 1 else 0) (List.range n))) = (Nat.ofDigits 2 (List.map (fun i => if i ∈ y then 1 else 0) (List.range n))) := by
      have h_binary_eq : (∑ i ∈ Finset.range n, (if i ∈ x then 2^i else 0)) = (∑ i ∈ Finset.range n, (if i ∈ y then 2^i else 0)) := by
        simp_all +decide [ Finset.sum_ite ];
        rw [ Finset.inter_eq_right.mpr hx, Finset.inter_eq_right.mpr hy, hsum_eq ];
      convert h_binary_eq using 1;
      · induction' n with n ih;
        · rfl;
        · induction' n + 1 with n ih <;> simp_all +decide [ Nat.ofDigits, Finset.sum_range_succ ];
          simp_all +decide [ Nat.ofDigits_append, List.range_succ ];
          rw [ Finset.range_add_one, Finset.inter_comm ];
          by_cases hn : n ∈ x <;> simp +decide [ hn, Finset.inter_comm, Finset.sum_insert ];
          ring;
      · induction' n with n ih <;> simp_all +decide [ Nat.ofDigits, Finset.sum_range_succ' ];
        induction' n + 1 with n ih <;> simp_all +decide [ Nat.ofDigits, Finset.sum_range_succ, List.range_succ ];
        simp_all +decide [ Nat.ofDigits_append, Finset.sum_range_succ, Finset.inter_comm ];
        rw [ Finset.range_add_one, Finset.inter_comm ];
        by_cases hn : n ∈ y <;> simp +decide [ hn, Finset.inter_comm, Finset.sum_insert ];
        ring;
    have h_binary_eq : List.map (fun i => if i ∈ x then 1 else 0) (List.range n) = List.map (fun i => if i ∈ y then 1 else 0) (List.range n) := by
      have h_binary_eq : ∀ {l1 l2 : List ℕ}, (∀ i ∈ l1, i = 0 ∨ i = 1) → (∀ i ∈ l2, i = 0 ∨ i = 1) → List.length l1 = List.length l2 → Nat.ofDigits 2 l1 = Nat.ofDigits 2 l2 → l1 = l2 := by
        intros l1 l2 hl1 hl2 hlen hsum_eq; induction' l1 with d1 l1 ih generalizing l2 <;> induction' l2 with d2 l2 ih' <;> simp_all +decide [ Nat.ofDigits ] ;
        exact ⟨ by omega, ih hl2.2 ( by linarith ) ( by omega ) ⟩;
      exact h_binary_eq ( fun i hi => by rw [ List.mem_map ] at hi; rcases hi with ⟨ i, _, rfl ⟩ ; by_cases hi' : i ∈ x <;> simp +decide [ hi' ] ) ( fun i hi => by rw [ List.mem_map ] at hi; rcases hi with ⟨ i, _, rfl ⟩ ; by_cases hi' : i ∈ y <;> simp +decide [ hi' ] ) ( by simp +decide ) ‹_›;
    simp_all +decide [ funext_iff, List.map_eq_map_iff ];
    grind;
  intro x y hxy; specialize @h_unique_binary ( Finset.image ( fun i : Fin n => ( i : ℕ ) ) x ) ( Finset.image ( fun i : Fin n => ( i : ℕ ) ) y ) ; simp_all +decide [ Finset.subset_iff ] ;
  simp_all +decide [ Finset.sum_image, Fin.val_injective.eq_iff ];
  exact Finset.image_injective ( fun a b h => by simpa [ Fin.ext_iff ] using h ) ( h_unique_binary hxy )

-- ==========================================
-- ORDER PROPERTIES
-- ==========================================

lemma simplicialLe_refl {n : ℕ} (a : Cube n) : simplicialLe a a := by
  unfold simplicialLe
  right
  exact ⟨rfl, le_rfl⟩

lemma simplicialLe_trans {n : ℕ} (a b c : Cube n)
    (hab : simplicialLe a b) (hbc : simplicialLe b c) : simplicialLe a c := by
  unfold simplicialLe at *
  rcases hab with hab_lt | ⟨hab_eq, hab_nat⟩
  · rcases hbc with hbc_lt | ⟨hbc_eq, _⟩
    · left; omega
    · left; omega
  · rcases hbc with hbc_lt | ⟨hbc_eq, hbc_nat⟩
    · left; omega
    · right
      constructor
      · omega
      · exact le_trans hab_nat hbc_nat

lemma simplicialLe_antisymm {n : ℕ} (a b : Cube n)
    (hab : simplicialLe a b) (hba : simplicialLe b a) : a = b := by
  unfold simplicialLe at hab hba
  rcases hab with h_a_lt_b | ⟨h_card_eq, h_nat_le⟩
  · rcases hba with h_b_lt_a | ⟨h_card_eq2, _⟩
    · omega
    · omega
  · rcases hba with h_b_lt_a | ⟨_, h_nat_le2⟩
    · omega
    · have h_nat_eq : cubeToNat a = cubeToNat b := le_antisymm h_nat_le h_nat_le2
      exact cubeToNat_inj h_nat_eq

lemma simplicialLe_total {n : ℕ} (a b : Cube n) : simplicialLe a b ∨ simplicialLe b a := by
  unfold simplicialLe
  rcases lt_trichotomy a.card b.card with h_lt | h_eq | h_gt
  · left; left; exact h_lt
  · rcases le_total (cubeToNat a) (cubeToNat b) with h_nat_le | h_nat_ge
    · left; right; exact ⟨h_eq, h_nat_le⟩
    · right; right; exact ⟨h_eq.symm, h_nat_ge⟩
  · right; left; exact h_gt

-- ==========================================
-- 7. INITIAL SEGMENT
-- ==========================================

noncomputable def rank {n : ℕ} (x : Cube n) : ℕ :=
  (Finset.univ.filter (fun y => simplicialLt y x)).card

noncomputable def simplicialInitSeg (n : ℕ) (k : ℕ) : Finset (Cube n) :=
  Finset.univ.filter (fun x => rank x < k)

-- ==========================================
-- 11. DIMENSIONAL SLICING (n → n + 1)
-- ==========================================

-- Embedding 0: Take vertex from n-cube, append 0 (no new bit)
noncomputable def embed0 {n : ℕ} (x : Cube n) : Cube (n + 1) :=
  x.image Fin.castSucc

-- Embedding 1: Take vertex from n-cube, append 1 (add last bit)
noncomputable def embed1 {n : ℕ} (x : Cube n) : Cube (n + 1) :=
  insert (Fin.last n) (x.image Fin.castSucc)

-- Lower slice (A₀): all x from n-cube whose embed0 is in A
noncomputable def slice0 {n : ℕ} (A : Finset (Cube (n + 1))) : Finset (Cube n) :=
  Finset.univ.filter (fun x => embed0 x ∈ A)

-- Upper slice (A₁): all x from n-cube whose embed1 is in A
noncomputable def slice1 {n : ℕ} (A : Finset (Cube (n + 1))) : Finset (Cube n) :=
  Finset.univ.filter (fun x => embed1 x ∈ A)

-- Lemma 11.1: Size of set equals sum of slice sizes
lemma slice_card_add {n : ℕ} (A : Finset (Cube (n + 1))) :
    (slice0 A).card + (slice1 A).card = A.card := by
  sorry

-- ==========================================
-- Helpers for neighborhood_succ
-- ==========================================

lemma hDist_embed0_embed0 {n : ℕ} (x y : Cube n) :
    hDist (embed0 x) (embed0 y) = hDist x y := by
  sorry

lemma hDist_embed1_embed1 {n : ℕ} (x y : Cube n) :
    hDist (embed1 x) (embed1 y) = hDist x y := by
  sorry

lemma hDist_embed0_embed1 {n : ℕ} (x y : Cube n) :
    hDist (embed0 x) (embed1 y) = hDist x y + 1 := by
  sorry

lemma slice0_neighborhood {n : ℕ} (A : Finset (Cube (n + 1))) :
    slice0 (neighborhood 1 A) = neighborhood 1 (slice0 A) ∪ slice1 A := by
  sorry

lemma slice1_neighborhood {n : ℕ} (A : Finset (Cube (n + 1))) :
    slice1 (neighborhood 1 A) = neighborhood 1 (slice1 A) ∪ slice0 A := by
  sorry

-- Lemma 11.2: Boundary Decomposition
lemma neighborhood_succ {n : ℕ} (A : Finset (Cube (n + 1))) :
    (neighborhood 1 A).card =
    (neighborhood 1 (slice0 A) ∪ slice1 A).card +
    (neighborhood 1 (slice1 A) ∪ slice0 A).card := by
  sorry

-- ==========================================
-- Helpers for initial_segment_optimal
-- ==========================================

-- Function H(n, k): Size of the boundary of an ideal initial segment
noncomputable def H (n k : ℕ) : ℕ :=
  (neighborhood 1 (simplicialInitSeg n k)).card

-- Basic algebraic properties of H
lemma H_zero (n : ℕ) : H n 0 = 0 := by
  sorry

lemma H_mono {n a b : ℕ} (h : a ≤ b) : H n a ≤ H n b := by
  sorry

lemma H_ge_self (n k : ℕ) : k ≤ H n k := by
  sorry

-- Translation of set unions to algebraic maximums
lemma initSeg_nested {n : ℕ} {k m : ℕ} (h : k ≤ m) :
    simplicialInitSeg n k ⊆ simplicialInitSeg n m := by
  sorry

lemma card_initSeg_union {n a b : ℕ} :
    (simplicialInitSeg n a ∪ simplicialInitSeg n b).card = max a b := by
  sorry

-- Structural theorem: The boundary of an initial segment is an initial segment
lemma neighborhood_initSeg_eq {n k : ℕ} :
    neighborhood 1 (simplicialInitSeg n k) = simplicialInitSeg n (H n k) := by
  sorry

-- ==========================================
-- The Algebraic Core of Harper's Theorem
-- ==========================================

-- Macaulay-Harper inequality. Proved via induction on n and binomial cascades.
lemma H_inequality (n a b : ℕ) (ha : a ≤ 2^n) (hb : b ≤ 2^n) :
    H (n + 1) (a + b) ≤ max (H n a) b + max (H n b) a := by
  sorry

-- ==========================================
-- Optimality of the initial segment
-- ==========================================

lemma initial_segment_optimal {n : ℕ} (k0 k1 : ℕ) (hk0 : k0 ≤ 2^n) (hk1 : k1 ≤ 2^n) :
    (neighborhood 1 (simplicialInitSeg (n + 1) (k0 + k1))).card ≤
    (neighborhood 1 (simplicialInitSeg n k0) ∪ simplicialInitSeg n k1).card +
    (neighborhood 1 (simplicialInitSeg n k1) ∪ simplicialInitSeg n k0).card := by
  change H (n + 1) (k0 + k1) ≤ _
  rw [neighborhood_initSeg_eq, neighborhood_initSeg_eq]
  rw [card_initSeg_union, card_initSeg_union]
  exact H_inequality n k0 k1 hk0 hk1

-- ==========================================
-- 12. FINAL HARPER'S THEOREM (By Dimension Induction)
-- ==========================================

theorem harper_theorem (n : ℕ) (A : Finset (Cube n)) (k : ℕ) (hk : A.card = k) :
    (neighborhood 1 (simplicialInitSeg n k)).card ≤ (neighborhood 1 A).card := by
  revert A k
  induction' n with n ih

  · -- Base case: dimension 0
    sorry

  · -- Inductive step: n to n + 1
    intro A k hk
    let A0 := slice0 A
    let A1 := slice1 A
    let k0 := A0.card
    let k1 := A1.card

    -- Apply Inductive Hypothesis to the slices
    have ih0 := ih A0 k0 rfl
    have ih1 := ih A1 k1 rfl

    -- Use the decomposition of the neighborhood in n+1 dimensions
    calc (neighborhood 1 (simplicialInitSeg (n + 1) k)).card
      _ = (neighborhood 1 (simplicialInitSeg (n + 1) (k0 + k1))).card := by
          rw [← hk, ← slice_card_add A]

      _ ≤ (neighborhood 1 (simplicialInitSeg n k0) ∪ simplicialInitSeg n k1).card +
          (neighborhood 1 (simplicialInitSeg n k1) ∪ simplicialInitSeg n k0).card := by
          apply initial_segment_optimal k0 k1 <;> sorry

      _ ≤ (neighborhood 1 A0 ∪ A1).card + (neighborhood 1 A1 ∪ A0).card := by
          sorry

      _ = (neighborhood 1 A).card := by
          rw [neighborhood_succ A]
