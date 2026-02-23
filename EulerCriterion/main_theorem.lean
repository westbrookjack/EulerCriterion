import Mathlib

open Polynomial


/-- Every `a : K` gives a root `algebraMap a` of `frobPoly K`. -/
noncomputable def frobPoly (K : Type*) [Field K] [Fintype K] :
    Polynomial (AlgebraicClosure K) :=
  X ^ (Fintype.card K) - X




lemma prime_char_of_finite_field
    (K : Type*) [Field K] [Finite K] (hchar : ringChar K ≠ 2) :
    (ringChar K) % 2 = 1 := by
  have h : Nat.Prime (ringChar K) := by
    exact CharP.prime_ringChar K
  refine Nat.mod_two_not_eq_zero.mp ?_
  by_contra hmod
  have cRingChar : ringChar K = 2 := by
    rw [← propext (Nat.Prime.even_iff h)]
    exact Nat.even_iff.mpr hmod
  rw[cRingChar] at hchar
  tauto


lemma power_eq_self (K : Type*) [Field K]
    (a : K) (n : ℕ) (ha : a ≠ 0) (han : a ^ n = a) :
    a ^ (n-1) = 1 := by
  cases n with
  | zero => simp only [zero_tsub, pow_zero]
  | succ n =>
    simp only [add_tsub_cancel_right]
    rw [npow_add] at han
    simp only [pow_one] at han
    have : a^n *  a * a⁻¹ = a * a⁻¹ := by
      exact
        Eq.symm
          (CancelDenoms.derive_trans₂ rfl rfl
            (congrFun (congrArg HMul.hMul (id (Eq.symm han))) a⁻¹))
    rw[mul_assoc] at this
    have rw_inv: a * a⁻¹ = 1 :=
      CommGroupWithZero.mul_inv_cancel a ha
    rw[rw_inv] at this
    rw [mul_one] at this
    exact this


lemma power_comm_w_alg_hom {R S : Type*}
    [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (a : R) (n : ℕ) :
      f (a ^ n) = f a ^ n := by
  induction n with
    | zero => simp
    | succ n ih => simp [pow_succ, map_mul, ih]


lemma X_pow_card_sub_X_ne_zero
    (K : Type*) [Field K] [Fintype K] :
    (X : Polynomial (AlgebraicClosure K)) ^ (Fintype.card K)
    - (X : Polynomial (AlgebraicClosure K)) ≠ 0 := by
  set q : ℕ := Fintype.card K
  have hq1 : q ≠ 1 := by
    have : 1 < q := Fintype.one_lt_card
    exact ne_of_gt this
  intro h
  have hc :
      ((X : Polynomial (AlgebraicClosure K)) ^ q
      - (X : Polynomial (AlgebraicClosure K))).coeff q = 0 := by
    simp only [h, coeff_zero]
  have hc' :
      ((X : Polynomial (AlgebraicClosure K)) ^ q
      - (X : Polynomial (AlgebraicClosure K))).coeff q = 1 := by
    simp only [coeff_sub, coeff_X_pow, ↓reduceIte, sub_eq_self, q]
    exact coeff_X_of_ne_one hq1
  rw[hc'] at hc
  norm_num at hc



/-- The degree computation: `natDegree (X^q - X) = q` for `q = card K`. -/
lemma natDegree_frobPoly_eq (K : Type*) [Field K] [Fintype K] :
    (frobPoly K).natDegree = Fintype.card K := by
  classical
  set q : ℕ := Fintype.card K
  have hf : frobPoly K ≠ 0 := by
    simpa [frobPoly] using (X_pow_card_sub_X_ne_zero K)
  have hcoeffq : (frobPoly K).coeff q = (1 : AlgebraicClosure K) := by
    have hq1 : q ≠ 1 := ne_of_gt (Fintype.one_lt_card : 1 < q)
    simp only [frobPoly, coeff_sub, coeff_X_pow, ↓reduceIte, sub_eq_self, q]
    exact coeff_X_of_ne_one hq1
  have hq_le : q ≤ (frobPoly K).natDegree := by
    have : (frobPoly K).coeff q ≠ (0 : AlgebraicClosure K) := by
      simp only [hcoeffq, ne_eq, one_ne_zero, not_false_eq_true]
    exact le_natDegree_of_ne_zero this
  have hle : (frobPoly K).natDegree ≤ q := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
    intro m hm
    have hm_ne1 : m ≠ 1 := by
      have : 1 < q := (Fintype.one_lt_card : 1 < q)
      exact by
        intro h1
        rw[h1] at hm
        have : q < q := Nat.lt_trans hm this
        norm_num at this
    simp only [frobPoly, coeff_sub, coeff_X_pow, hm.ne', ↓reduceIte, zero_sub, neg_eq_zero, q]
    exact coeff_X_of_ne_one hm_ne1
  exact le_antisymm (by simpa [q] using hle) (by simpa [q] using hq_le)


lemma roots_of_frob_poly
    (K : Type*) [Field K] [Fintype K]
    (a : K) :
    algebraMap K (AlgebraicClosure K) a
      ∈ (frobPoly K).roots := by
  simp only [frobPoly]
  rw [mem_roots]
  · simp only [IsRoot.def, eval_sub, eval_pow, eval_X]
    rw[← power_comm_w_alg_hom
          (algebraMap K (AlgebraicClosure K)),
        FiniteField.pow_card a]
    simp only [sub_self]
  · exact X_pow_card_sub_X_ne_zero K


noncomputable def imgK
    (K : Type*) [Field K] [Fintype K] :
    Set (AlgebraicClosure K) :=
  (algebraMap K (AlgebraicClosure K)) '' Set.univ


-- Finset version of your image (for counting only)

noncomputable def imgKFinset
    (K : Type*) [Field K] [Fintype K] :
    Finset (AlgebraicClosure K) :=
  haveI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
  (Finset.univ : Finset K).image
    (algebraMap K (AlgebraicClosure K))


lemma card_imgKFinset
    (K : Type*) [Field K] [Fintype K] :
    (imgKFinset K).card = Fintype.card K := by
  classical
  have hinj :
      Function.Injective
        (algebraMap K (AlgebraicClosure K)) :=
    (algebraMap K (AlgebraicClosure K)).injective
  simpa [imgKFinset] using
    (Finset.card_image_of_injective
      (s := (Finset.univ : Finset K))
      hinj)
--Without this classical, since the algebraic closure is not decidable, the image of the finset
--is not a finset, and we can't talk about its cardinality.
section
attribute [local instance] Classical.decEq

lemma imgKFinset_subset_roots
    (K : Type*) [Field K] [Fintype K] :
    imgKFinset K ⊆ (frobPoly K).roots.toFinset := by
  intro x hx
  rcases (by
    simpa [imgKFinset] using hx
  ) with ⟨a, _ha, rfl⟩
  exact Multiset.mem_toFinset.mpr (roots_of_frob_poly K a)


#check Finset.eq_of_subset_of_card_le

lemma card_roots_lower_bound
    (K : Type*) [Field K] [Fintype K] :
    Fintype.card K ≤
      (frobPoly K).roots.toFinset.card := by
  have hsubset := imgKFinset_subset_roots K
  have := Finset.card_le_card hsubset
  simpa [card_imgKFinset K] using this




lemma card_roots_upper_bound
    (K : Type*) [Field K] [Fintype K] :
    (frobPoly K).roots.toFinset.card ≤
      (frobPoly K).natDegree := by
  have hf : frobPoly K ≠ 0 := by
    simpa [frobPoly]
      using X_pow_card_sub_X_ne_zero K
  have h1 : (frobPoly K).roots.toFinset.card ≤ (frobPoly K).roots.card :=
    Multiset.toFinset_card_le _
  have h2 : (frobPoly K).roots.card ≤ (frobPoly K).natDegree :=
    card_roots' (frobPoly K)
  exact le_trans h1 h2






lemma card_roots_frobPoly
    (K : Type*) [Field K] [Fintype K] :
    (frobPoly K).roots.toFinset.card =
      Fintype.card K := by
  classical
  have hl := card_roots_lower_bound K
  have hu := card_roots_upper_bound K
  have hd := natDegree_frobPoly_eq K
  exact le_antisymm
    (by simpa [hd] using hu)
    hl





lemma mem_roots_frobPoly (K : Type*) [Field K] [Fintype K] :
   (frobPoly K).roots.toFinset = imgKFinset K := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · exact imgKFinset_subset_roots K
  · rw[card_roots_frobPoly K, card_imgKFinset K]



theorem image_criterion (K : Type*) [Field K] [Fintype K] (b : AlgebraicClosure K) :
     (∃ a : K, b = algebraMap K (AlgebraicClosure K) a ) ↔ b ^ (Fintype.card K ) = b := by
  constructor
  · intro h
    rcases h with ⟨a, ha⟩
    rw[ha]
    rw[← power_comm_w_alg_hom (algebraMap K (AlgebraicClosure K)) a (Fintype.card K)]
    rw[ FiniteField.pow_card a]
  · intro h
    have : b ∈ (frobPoly K).roots := by
      simp only [frobPoly]
      rw [mem_roots]
      · simp only [IsRoot.def, eval_sub, eval_pow, eval_X]
        rw [h]
        norm_num
      · exact X_pow_card_sub_X_ne_zero K
    have : b ∈ imgKFinset K := by
      have : b ∈ (frobPoly K).roots.toFinset := Multiset.mem_toFinset.mpr this
      rwa[mem_roots_frobPoly K] at this
    rw[imgKFinset] at this
    rcases Finset.mem_image.mp this with ⟨c, hc, rfl⟩
    use c

end



theorem forward_direction (K : Type*) [Field K] [Fintype K] (hchar : ringChar K ≠ 2) (a : K)
    : a ^ ((Fintype.card K - 1) / 2) = 1  → ∃ b : K, a = b ^ 2 := by
  intro h
  let a' : AlgebraicClosure K :=
    algebraMap K (AlgebraicClosure K) a
  have : ∃ b : (AlgebraicClosure K), a'  = b * b := by
    exact IsAlgClosed.exists_eq_mul_self a'
  have ha' : a' ^ ((Fintype.card K - 1) / 2) = 1 := by
    simp only [a']
    rw[← power_comm_w_alg_hom (algebraMap K (AlgebraicClosure K)) a ((Fintype.card K - 1) / 2), h]
    exact algebraMap.coe_one
  rcases this with ⟨b, hb⟩
  rw[Eq.symm (pow_two b)] at hb
  rw[hb] at ha'
  have (m n : ℕ) : (b^m)^n = b^(m * n) := by exact Eq.symm (pow_mul b m n)
  rw[← pow_mul b 2 ((Fintype.card K -1 )/ 2), mul_comm] at ha'
  have :  ((Fintype.card K - 1) / 2) * 2 = Fintype.card K - 1 := by
    rw [← Nat.dvd_iff_div_mul_eq]
    have hcharconversion: CharP K (ringChar K) := ringChar.charP K
    have : ∃ (n : ℕ+), Nat.Prime (ringChar K) ∧ Fintype.card K = (ringChar K) ^ (n : ℕ) :=
      FiniteField.card K (ringChar K)
    rcases this with ⟨n, hprime, hcard⟩
    rw[hcard]
    have hoddpow : (ringChar K) ^ (n : ℕ) % 2 = 1 := by
      rw [Nat.pow_mod]
      rw [prime_char_of_finite_field K hchar]
      norm_num
    have : ((ringChar K) ^ (n : ℕ) -1) % 2 = 0 := Nat.sub_mod_eq_zero_of_mod_eq hoddpow
    exact Nat.dvd_of_mod_eq_zero this
  rw[this] at ha'
  have hKcard_ne_zero : Fintype.card K ≠ 0 := by
    have : 0 < Fintype.card K := Fintype.card_pos
    exact ne_of_gt this
  have hb' : b ^ (Fintype.card K) = b := by
    by_cases Fintype.card K = 0
    · tauto
    · have (n : ℕ)(hn : n ≠ 0) : b ^ n = b ^ (n-1) * b := by
        exact Eq.symm (pow_sub_one_mul hn b)
      rw[this (Fintype.card K) hKcard_ne_zero, ha']
      norm_num
  rw[ ← image_criterion K b] at hb'
  rcases hb' with ⟨c, hc⟩
  use c
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw[power_comm_w_alg_hom (algebraMap K (AlgebraicClosure K)) c 2, ← hc, ← hb]












theorem euler_criterion
    (K : Type*) [Field K] [Fintype K]
    (a : K) (ha : a ≠ 0) (hchar : ringChar K ≠ 2) :
    IsSquare a ↔ a ^ ((Fintype.card K - 1) / 2) = 1 := by
  constructor
  · intro h
    rcases h with ⟨b, hb⟩
    rw[← sq] at hb
    rw[hb]
    have hcharodd : (ringChar K) % 2 = 1 := prime_char_of_finite_field K hchar
    have : (Fintype.card K - 1) / 2 * 2 = Fintype.card K - 1 := by
      rw [← Nat.dvd_iff_div_mul_eq]
      have hcharconversion: CharP K (ringChar K) := ringChar.charP K
      have : ∃ (n : ℕ+), Nat.Prime (ringChar K) ∧ Fintype.card K = (ringChar K) ^ (↑n : ℕ) :=
        FiniteField.card K (ringChar K)
      rcases this with ⟨n, hprime, hcard⟩
      rw[hcard]
      have hoddpow : (ringChar K) ^ (↑n : ℕ) % 2 = 1 := by
        rw [Nat.pow_mod]
        rw [hcharodd]
        norm_num
      have : ((ringChar K) ^ (↑n : ℕ) -1) % 2 = 0 := Nat.sub_mod_eq_zero_of_mod_eq hoddpow
      exact Nat.dvd_of_mod_eq_zero this
    rw[Eq.symm (pow_mul' b ((Fintype.card K - 1) / 2) 2), this]
    have : b^(Fintype.card K) = b := FiniteField.pow_card b
    have hbnonzero : b ≠ 0 := by
      by_contra hzero
      rw[hzero] at hb
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hb
      tauto
    exact power_eq_self K b (Fintype.card K) hbnonzero this
  · intro h
    have :=  forward_direction K hchar a h
    rcases this with ⟨b, hb⟩
    use b
    rw[hb]
    exact pow_two b
