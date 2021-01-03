import measure_theory.haar_measure
import measure_theory.prod

open topological_space function set
open_locale ennreal

/- todo: make `regular` a type class? -/

namespace topological_space

variables (α : Type*) [topological_space α]

/-- A σ-compact space is a space that is the union of a countable collection of compact subspaces.
  Note that a locally compact separable T₂ space need not be σ-compact.
  The sequence can be extracted using `topological_space.compact_covering`.
  -/
class sigma_compact_space (α : Type*) [topological_space α] : Prop :=
(exists_compact_covering : ∃ K : ℕ → set α, (∀ n, is_compact (K n)) ∧ (⋃ n, K n) = univ)

variables [sigma_compact_space α]
open sigma_compact_space
/-- A compact covering of a σ-compact space -/
def compact_covering : ℕ → set α :=
classical.some exists_compact_covering

lemma is_compact_compact_covering (n : ℕ) : is_compact (compact_covering α n) :=
(classical.some_spec sigma_compact_space.exists_compact_covering).1 n

lemma Union_compact_covering : (⋃ n, compact_covering α n) = univ :=
(classical.some_spec sigma_compact_space.exists_compact_covering).2

variables (G : Type*) [group G] [topological_space G] [topological_group G]
variables [separable_space G]

/-- Every locally compact separable topological group is σ-compact.
  This means that it is the union of a countable collection of compact subspaces.
  Note: this is not true if we drop the topological group hypothesis. -/
lemma exists_compact_covering [locally_compact_space G] :
  ∃ K : ℕ → set G, (∀ n, is_compact (K n)) ∧ (⋃ n, K n) = univ :=
begin
  obtain ⟨L, h1L, h2L, h3L⟩ := exists_compact_subset is_open_univ (mem_univ (1 : G)),
  refine ⟨λ n, (λ x, x * dense_seq G n) ⁻¹' L, _, _⟩,
  { intro n, exact (homeomorph.mul_right _).compact_preimage.mpr h1L },
  { rw [eq_univ_iff_forall],
    intro x,
    obtain ⟨_, hn, ⟨n, rfl⟩⟩ : ((λ y, x * y) ⁻¹' L ∩ range (dense_seq G)).nonempty :=
    (dense_iff_inter_open.mp (dense_range_dense_seq G) _
      ((homeomorph.mul_left _).continuous.is_open_preimage _ is_open_interior)
      ⟨x⁻¹, by simp [homeomorph.mul_left, h2L]⟩).mono
      (inter_subset_inter_left _ $ preimage_mono $ interior_subset),
    rw [mem_Union], exact ⟨n, hn⟩ }
end

end topological_space
open topological_space

namespace ennreal

protected lemma measurable_inv : measurable (has_inv.inv : ennreal → ennreal) :=
ennreal.continuous_inv.measurable

protected lemma measurable_div : measurable (λ p : ennreal × ennreal, p.1 / p.2) :=
ennreal.measurable_mul.comp $ measurable_fst.prod_mk $ ennreal.measurable_inv.comp measurable_snd

end ennreal

section

variables {α β : Type*} [measurable_space α] [measurable_space β]

lemma measurable.ennreal_inv {f : α → ennreal} (hf : measurable f) : measurable (λ a, (f a)⁻¹) :=
ennreal.measurable_inv.comp hf

lemma measurable.ennreal_div {f g : α → ennreal} (hf : measurable f) (hg : measurable g) :
  measurable (λ a, f a / g a) :=
ennreal.measurable_div.comp $ hf.prod_mk hg

end

namespace measure_theory

namespace measure

section prod

variables {α β : Type*} [measurable_space α] [measurable_space β] {μ : measure α} {ν : measure β}


lemma lintegral_lintegral_mul {f : α → ennreal} {g : β → ennreal} (hf : measurable f)
  (hg : measurable g) : ∫⁻ x, ∫⁻ y, f x * g y ∂ν ∂μ = ∫⁻ x, f x ∂μ * ∫⁻ y, g y ∂ν :=
by simp [lintegral_const_mul _ hg, lintegral_mul_const _ hf]

variable [sigma_finite ν]
lemma lintegral_prod_mul {f : α → ennreal} {g : β → ennreal} (hf : measurable f)
  (hg : measurable g) : ∫⁻ z, f z.1 * g z.2 ∂(μ.prod ν) = ∫⁻ x, f x ∂μ * ∫⁻ y, g y ∂ν :=
by simp [lintegral_prod _ ((hf.comp measurable_fst).ennreal_mul $ hg.comp measurable_snd),
  lintegral_lintegral_mul hf hg]

end prod

variables {G : Type*} [group G] [topological_space G] [topological_group G]
variables [measurable_space G] [borel_space G]
variables {μ ν : measure G}

section separable

variables [t2_space G] [separable_space G] [locally_compact_space G]

/-- If we define σ-compact spaces, we could easily prove this for those. -/
lemma regular.sigma_finite (hμ : regular μ) : sigma_finite μ :=
let ⟨K, h1K, h2K⟩ := exists_compact_covering G in
⟨{ set := K,
  set_mem := λ n, (h1K n).is_measurable,
  finite := λ n, hμ.lt_top_of_is_compact $ h1K n,
  spanning := h2K }⟩

instance (K₀ : positive_compacts G) : sigma_finite (haar_measure K₀) :=
regular_haar_measure.sigma_finite

end separable

variables [second_countable_topology G]

lemma is_left_invariant_lintegral (hμ : is_left_invariant μ) {f : G → ennreal} (hf : measurable f)
  (y : G) : ∫⁻ x, f (y * x) ∂μ = ∫⁻ x, f x ∂μ :=
begin
  conv_rhs { rw [← map_mul_left_eq_self.mpr hμ y] },
  rw [lintegral_map hf], exact measurable_const.mul measurable_id,
end


variables [t2_space G]

variables [sigma_finite ν] [sigma_finite μ]

lemma measure_inv_ne_zero (hμ : is_left_invariant μ) {E : set G} (hE : is_measurable E) (h2E : μ E ≠ 0) :
  μ ((λ x, x⁻¹) ⁻¹' E) ≠ 0 :=
begin
  sorry
end

lemma measure_inv_ne_top (hμ : is_left_invariant μ) {E : set G} (hE : is_measurable E) (h2E : μ E ≠ ⊤) :
  μ ((λ x, x⁻¹) ⁻¹' E) ≠ ⊤ :=
begin
  sorry
end

lemma measure_mul_right_ne_zero (hμ : is_left_invariant μ) {E : set G} (hE : is_measurable E) (h2E : μ E ≠ 0) (y : G) :
  μ ((λ x, x * y) ⁻¹' E) ≠ 0 :=
begin
  sorry
end

lemma measure_mul_right_ne_top (hμ : is_left_invariant μ) {E : set G} (hE : is_measurable E) (h2E : μ E ≠ ⊤) (y : G) :
  μ ((λ x, x * y) ⁻¹' E) ≠ ⊤ :=
begin
  sorry
end

lemma measurable_measure_mul_right (hμ : is_left_invariant μ) {E : set G} (hE : is_measurable E) :
  measurable (λ x, μ ((λ y, y * x) ⁻¹' E)) :=
begin
  sorry
end

lemma lintegral_lintegral_mul_inv (hμ : is_left_invariant μ) (hν : is_left_invariant ν) (f : G → G → ennreal) (hf : measurable (uncurry f)) :
  ∫⁻ x, ∫⁻ y, f (y * x) x⁻¹ ∂ν ∂μ = ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ :=
begin
  symmetry,
  conv_lhs { congr, skip, funext, rw [← is_left_invariant_lintegral hν hf.of_uncurry_left x⁻¹] },
  simp_rw [lintegral_lintegral_swap (show measurable (uncurry (λ (x y : G), f x (x⁻¹ * y))), from
    hf.comp (measurable_fst.prod_mk $ measurable_fst.inv.mul measurable_snd))],
  -- the following double-show is a bit ugly, but the `rw` cares a lot about the formulation of the
  -- argument, and the elaborator has trouble when given the first type.
  conv_lhs { congr, skip, funext,
    rw [← is_left_invariant_lintegral hμ (show measurable (λ x, f x (x⁻¹ * y)), from
      show measurable (uncurry f ∘ λ (x : G), (x, x⁻¹ * y)), from
      hf.comp (measurable_id.prod_mk $ measurable_inv.mul measurable_const)) y] },
  simp_rw [mul_inv_rev, inv_mul_cancel_right],
  rw [lintegral_lintegral_swap],
  exact hf.comp ((measurable_fst.mul measurable_snd).prod_mk measurable_snd.inv)
end

/-! We follow the book Measure Theory by Donald Cohn. -/

/-- [Cohn, §60 Th. A] -/
lemma measure_lintegral_div_measure (hμ : is_left_invariant μ) (hν : is_left_invariant ν) {E : set G} (hE : is_measurable E) (h2E : ν E ≠ 0)
  (h3E : ν E ≠ ∞) (f : G → ennreal) (hf : measurable f) :
  μ E * ∫⁻ y, f y⁻¹ / ν ((λ h, h * y⁻¹) ⁻¹' E) ∂ν = ∫⁻ x, f x ∂μ :=
begin
  symmetry,
  set g := λ y, f y⁻¹ / ν ((λ h, h * y⁻¹) ⁻¹' E),
  have hg : measurable g := (hf.comp measurable_inv).ennreal_div
    ((measurable_measure_mul_right hν hE).comp measurable_inv),
  simp_rw [← set_lintegral_one, ← lintegral_indicator _ hE,
    ← lintegral_lintegral_mul (measurable_const.indicator hE) hg],
  rw [← lintegral_lintegral_mul_inv hμ hν],
  have mE : ∀ x : G, measurable (λ y, ((λ z, z * x) ⁻¹' E).indicator (λ z, (1 : ennreal)) y) :=
  λ x, measurable_const.indicator (measurable_mul_right _ hE),
  have : ∀ x y, E.indicator (λ (z : G), (1 : ennreal)) (y * x) =
    ((λ z, z * x) ⁻¹' E).indicator (λ (b : G), 1) y,
  { intros x y, symmetry, convert indicator_comp_right (λ y, y * x), ext1 z, simp },
  simp_rw [this, lintegral_mul_const _ (mE _), lintegral_indicator _ (measurable_mul_right _ hE),
    set_lintegral_one, g, inv_inv,
    ennreal.mul_div_cancel' (measure_mul_right_ne_zero hν hE h2E _)
      (measure_mul_right_ne_top hν hE h3E _)],
  exact ((measurable_const.indicator hE).comp measurable_fst).ennreal_mul (hg.comp measurable_snd)
end

lemma measure_mul_measure_eq (hμ : is_left_invariant μ) (hν : is_left_invariant ν) {E F : set G} (hE : is_measurable E) (hF : is_measurable F)
  (h2E : ν E ≠ 0) (h3E : ν E ≠ ∞) : μ E * ν F = ν E * μ F :=
begin
  have h1 := measure_lintegral_div_measure hν hν hE h2E h3E (F.indicator (λ x, 1))
    (measurable_const.indicator hF),
  have h2 := measure_lintegral_div_measure hμ hν hE h2E h3E (F.indicator (λ x, 1))
    (measurable_const.indicator hF),
  rw [lintegral_indicator _ hF, set_lintegral_one] at h1 h2,
  rw [← h1, mul_left_comm, h2],
end

variables [locally_compact_space G] [sigma_compact_space G]

theorem haar_measure_unqiue (hμ : is_left_invariant μ) (K₀ : positive_compacts G) :
  μ = μ K₀.1 • haar_measure K₀ :=
begin
  ext1 s hs,
  have := measure_mul_measure_eq hμ (is_left_invariant_haar_measure K₀) K₀.2.1.is_measurable hs,
  rw [haar_measure_self, one_mul] at this,
  rw [← this (by norm_num) (by norm_num), smul_apply],
end

end measure

-- #lint

end measure_theory
