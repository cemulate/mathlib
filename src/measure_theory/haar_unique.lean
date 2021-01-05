import measure_theory.haar_measure
import measure_theory.prod

open topological_space function set
open_locale ennreal

/- todo: make `regular` a type class? -/

-- make measure.prod irreducible (and measure.pi)

namespace set

variables {α β γ δ : Type*} {s : set α} {t : set β}

lemma prod_preimage_left {f : γ → α} : (f ⁻¹' s).prod t = (λp, (f p.1, p.2)) ⁻¹' (s.prod t) := rfl

lemma prod_preimage_right {g : δ → β} : s.prod (g ⁻¹' t) = (λp, (p.1, g p.2)) ⁻¹' (s.prod t) := rfl

lemma mk_preimage_prod_left_fn_eq_if {y : β} [decidable_pred (∈ t)] (f : γ → α) :
  (λ x, (f x, y)) ⁻¹' s.prod t = if y ∈ t then f ⁻¹' s else ∅ :=
by rw [← mk_preimage_prod_left_eq_if, prod_preimage_left, preimage_preimage]

lemma mk_preimage_prod_right_fn_eq_if {x : α} [decidable_pred (∈ s)] (g : δ → β) :
  (λ y, (x, g y)) ⁻¹' s.prod t = if x ∈ s then g ⁻¹' t else ∅ :=
by rw [← mk_preimage_prod_right_eq_if, prod_preimage_right, preimage_preimage]

lemma preimage_prod_mk_prod (f : γ → α) (g : γ → β) :
  (λ x, (f x, g x)) ⁻¹' s.prod t = f ⁻¹' s ∩ g ⁻¹' t :=
by { ext x, simp }


end set
open set

namespace equiv

variables {α β γ δ : Type*}
/-- A variation on `equiv.prod_congr` where the equivalence in the second component can depend
  on the first component. -/
@[simps {fully_applied := ff}]
def prod_twist {α₁ β₁ α₂ β₂ : Type*} (e₁ : α₁ ≃ α₂) (e₂ : α₁ → β₁ ≃ β₂) : α₁ × β₁ ≃ α₂ × β₂ :=
{ to_fun := λ x : α₁ × β₁, (e₁ x.1, e₂ x.1 x.2),
  inv_fun := λ y : α₂ × β₂, (e₁.symm y.1, (e₂ $ e₁.symm y.1).symm y.2),
  left_inv := by { rintro ⟨x₁, y₁⟩, simp only [symm_apply_apply] },
  right_inv := by { rintro ⟨x₁, y₁⟩, simp only [apply_symm_apply] } }

end equiv

section

variables {G : Type*} [topological_space G] [group G] [topological_group G]

variable (G)
/-- The map `(x, y) ↦ (x, xy)` as a homeomorphism. -/
@[to_additive prod_add_right "The map `(x, y) ↦ (x, x + y)` as a homeomorphism."]
protected def homeomorph.prod_mul_right : G × G ≃ₜ G × G :=
{ continuous_to_fun  := continuous_fst.prod_mk continuous_mul,
  continuous_inv_fun := continuous_fst.prod_mk $ continuous_fst.inv.mul continuous_snd,
  .. equiv.prod_twist (equiv.refl _) equiv.mul_left }

@[simp, to_additive homeomorph.prod_add_right_coe]
lemma homeomorph.prod_mul_right_coe :
  ⇑(homeomorph.prod_mul_right G) = λ z : G × G, (z.1, z.1 * z.2) :=
rfl

@[simp, to_additive homeomorph.prod_add_right_symm_coe]
lemma homeomorph.prod_mul_right_symm_coe :
  ⇑(homeomorph.prod_mul_right G).symm = λ z : G × G, (z.1, z.1⁻¹ * z.2) :=
rfl

variable {G}
end

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

/- CHOOSE ABOVE OR BELOW -/

instance locally_compact_group.sigma_compact_space [locally_compact_space G] :
  sigma_compact_space G :=
begin
  constructor,
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

section

/-- extra simp lemma that `dsimp` can use -/
@[simp, to_additive]
lemma mul_left_symm_apply {G} [group G] (a : G) : ((equiv.mul_left a).symm : G → G) = (*) a⁻¹ :=
rfl

/-- extra simp lemma that `dsimp` can use -/
@[simp, to_additive]
lemma mul_right_symm_apply {G} [group G] (a : G) :
  ((equiv.mul_right a).symm : G → G) = λ x, x * a⁻¹ :=
rfl

end

namespace measurable_equiv

variables {α β : Type*} [measurable_space α] [measurable_space β]

@[simp] theorem symm_comp_self (e : α ≃ᵐ β) : e.symm ∘ e = id := funext e.left_inv

@[simp] theorem self_comp_symm (e : α ≃ᵐ β) : e ∘ e.symm = id := funext e.right_inv


end measurable_equiv

section

variables {α : Type*} {β : Type*} [topological_space α]
  [measurable_space α] [borel_space α] [topological_space β] [measurable_space β]
  [borel_space β]

set_option trace.simps.verbose true

@[simp]
lemma homeomorph.to_measurable_equiv_coe (h : α ≃ₜ β) : (h.to_measurable_equiv : α → β) = h :=
rfl

@[simp] lemma homeomorph.to_measurable_equiv_symm_coe (h : α ≃ₜ β) :
  (h.to_measurable_equiv.symm : β → α) = h.symm :=
rfl


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

lemma map_symm_map (e : α ≃ᵐ β) : map e.symm (map e μ) = μ :=
by simp [map_map e.symm.measurable e.measurable]

lemma map_map_symm (e : α ≃ᵐ β) : map e (map e.symm ν) = ν :=
by simp [map_map e.measurable e.symm.measurable]

lemma map_measurable_equiv_injective (e : α ≃ᵐ β) : injective (map e) :=
by { intros μ₁ μ₂ hμ, apply_fun map e.symm at hμ, simpa [map_symm_map e] using hμ }

lemma map_apply_eq_iff_map_symm_apply_eq (e : α ≃ᵐ β) : map e μ = ν ↔ map e.symm ν = μ :=
by rw [← (map_measurable_equiv_injective e).eq_iff, map_map_symm, eq_comm]

end prod

variables {G : Type*} [group G] [topological_space G] [topological_group G]
variables [measurable_space G]
variables {μ ν : measure G}

section separable

-- lemma regular.sigma_finite [opens_measurable_space G] [t2_space G] [sigma_compact_space G] (hμ : regular μ) : sigma_finite μ :=
-- ⟨{ set := compact_covering G,
--   set_mem := λ n, (is_compact_compact_covering G n).is_measurable,
--   finite := λ n, hμ.lt_top_of_is_compact $ is_compact_compact_covering G n,
--   spanning := Union_compact_covering G }⟩

-- -- #print regular.sigma_finite
-- instance (K₀ : positive_compacts G) [borel_space G] [t2_space G] [locally_compact_space G] [sigma_compact_space G] : sigma_finite (haar_measure K₀) :=
-- regular_haar_measure.sigma_finite

/- CHOOSE ABOVE OR BELOW -/

variables [t2_space G] [separable_space G] [locally_compact_space G]

/-- If we define σ-compact spaces, we could easily prove this for those. -/
lemma regular.sigma_finite [opens_measurable_space G] (hμ : regular μ) : sigma_finite μ :=
let ⟨K, h1K, h2K⟩ := exists_compact_covering G in
⟨{ set := K,
  set_mem := λ n, (h1K n).is_measurable,
  finite := λ n, hμ.lt_top_of_is_compact $ h1K n,
  spanning := h2K }⟩




-- #print regular.sigma_finite
instance (K₀ : positive_compacts G) [borel_space G] : sigma_finite (haar_measure K₀) :=
regular_haar_measure.sigma_finite

end separable

variables [second_countable_topology G] [borel_space G]

lemma is_left_invariant_lintegral (hμ : is_left_invariant μ) {f : G → ennreal} (hf : measurable f)
  (y : G) : ∫⁻ x, f (y * x) ∂μ = ∫⁻ x, f x ∂μ :=
begin
  conv_rhs { rw [← map_mul_left_eq_self.mpr hμ y] },
  rw [lintegral_map hf], exact measurable_const.mul measurable_id,
end


variables [t2_space G]

variables [sigma_finite ν] [sigma_finite μ]


/-- This condition is part of the definition of a measurable group in [Halmos]. -/
lemma map_prod_mul_eq (hμ : is_left_invariant μ) (hν : is_left_invariant ν) :
  map (λ z : G × G, (z.1, z.1 * z.2)) (μ.prod ν) = μ.prod ν :=
begin
  refine (prod_eq _).symm, intros s t hs ht,
  simp_rw [map_apply (measurable_fst.prod_mk (measurable_fst.mul measurable_snd)) (hs.prod ht),
    prod_apply ((measurable_fst.prod_mk (measurable_fst.mul measurable_snd)) (hs.prod ht)),
    preimage_preimage],
  conv_lhs { congr, skip, funext, rw [mk_preimage_prod_right_fn_eq_if ((*) x), measure_if] },
  simp_rw [hν _ ht, lintegral_indicator _ hs, lintegral_const, restrict_apply_univ, mul_comm]
end

lemma map_prod_mul_eq_swap (hμ : is_left_invariant μ) (hν : is_left_invariant ν) :
  map (λ z : G × G, (z.2, z.2 * z.1)) (μ.prod ν) = ν.prod μ :=
begin
  rw [← prod_swap],
  simp_rw [map_map (measurable_snd.prod_mk (measurable_snd.mul measurable_fst)) measurable_swap],
  exact map_prod_mul_eq hν hμ
end

lemma map_prod_inv_mul_eq (hμ : is_left_invariant μ) (hν : is_left_invariant ν) :
  map (λ z : G × G, (z.1, z.1⁻¹ * z.2)) (μ.prod ν) = μ.prod ν :=
(map_apply_eq_iff_map_symm_apply_eq $ (homeomorph.prod_mul_right G).to_measurable_equiv).mp $
  map_prod_mul_eq hμ hν

lemma map_prod_inv_mul_eq_swap (hμ : is_left_invariant μ) (hν : is_left_invariant ν) :
  map (λ z : G × G, (z.2, z.2⁻¹ * z.1)) (μ.prod ν) = ν.prod μ :=
begin
  rw [← prod_swap],
  simp_rw [map_map (measurable_snd.prod_mk (measurable_snd.inv.mul measurable_fst)) measurable_swap],
  exact map_prod_inv_mul_eq hν hμ
end

lemma map_prod_mul_inv_eq (hμ : is_left_invariant μ) (hν : is_left_invariant ν) :
  map (λ z : G × G, (z.2 * z.1, z.1⁻¹)) (μ.prod ν) = μ.prod ν :=
begin
  let S := (homeomorph.prod_mul_right G).to_measurable_equiv,
  suffices : map ((λ z : G × G, (z.2, z.2⁻¹ * z.1)) ∘ (λ z : G × G, (z.2, z.2 * z.1))) (μ.prod ν) =
    μ.prod ν,
  { convert this, ext1 ⟨x, y⟩, simp },
  simp_rw [← map_map (measurable_snd.prod_mk (measurable_snd.inv.mul measurable_fst))
    (measurable_snd.prod_mk (measurable_snd.mul measurable_fst)), map_prod_mul_eq_swap hμ hν,
    map_prod_inv_mul_eq_swap hν hμ]
end

lemma measure_null_of_measure_inv_null (hμ : is_left_invariant μ) {E : set G} (hE : is_measurable E)
  (h2E : μ ((λ x, x⁻¹) ⁻¹' E) = 0) : μ E = 0 :=
begin
  have hf : measurable (λ z : G × G, (z.2 * z.1, z.1⁻¹)) :=
  ((measurable_snd.mul measurable_fst).prod_mk measurable_fst.inv),
  suffices : map (λ z : G × G, (z.2 * z.1, z.1⁻¹)) (μ.prod μ) (E.prod E) = 0,
  { simpa only [map_prod_mul_inv_eq hμ hμ, prod_prod hE hE, mul_eq_zero, or_self] using this },
  simp_rw [map_apply hf (hE.prod hE), prod_apply_symm (hf (hE.prod hE)), preimage_preimage,
    preimage_prod_mk_prod],
  convert lintegral_zero, ext1 x, refine measure_mono_null (inter_subset_right _ _) h2E
end

lemma measure_inv_null (hμ : is_left_invariant μ) {E : set G} (hE : is_measurable E) :
  μ ((λ x, x⁻¹) ⁻¹' E) = 0 ↔ μ E = 0 :=
begin
  refine ⟨measure_null_of_measure_inv_null hμ hE, _⟩,
  intro h2E, apply measure_null_of_measure_inv_null hμ (measurable_inv hE), convert h2E using 2,
  exact set.inv_inv
end

lemma measure_eq_top_of_measure_inv_eq_top (hμ : is_left_invariant μ) {E : set G}
  (hE : is_measurable E) (h2E : μ ((λ x, x⁻¹) ⁻¹' E) = ⊤) : μ E = ⊤ :=
begin
  -- have hf : measurable (λ z : G × G, (z.2 * z.1, z.1⁻¹)) :=
  -- ((measurable_snd.mul measurable_fst).prod_mk measurable_fst.inv),
  -- suffices : map (λ z : G × G, (z.2 * z.1, z.1⁻¹)) (μ.prod μ) (E.prod E) = ⊤,
  -- { simpa only [map_prod_mul_inv_eq hμ hμ, prod_prod hE hE, mul_eq_zero, or_self] using this },
  -- simp_rw [map_apply hf (hE.prod hE), prod_apply_symm (hf (hE.prod hE)), preimage_preimage,
  --   preimage_prod_mk_prod],
  -- convert lintegral_zero, ext1 x, refine measure_mono_null (inter_subset_right _ _) h2E
  sorry
end

lemma measure_inv_eq_top (hμ : is_left_invariant μ) {E : set G} (hE : is_measurable E) :
  μ ((λ x, x⁻¹) ⁻¹' E) = ⊤ ↔ μ E = ⊤ :=
begin
  refine ⟨measure_eq_top_of_measure_inv_eq_top hμ hE, _⟩,
  intro h2E, apply measure_eq_top_of_measure_inv_eq_top hμ (measurable_inv hE), convert h2E using 2,
  exact set.inv_inv
end

-- lemma measure_inv_ne_zero (hμ : is_left_invariant μ) {E : set G} (hE : is_measurable E) (h2E : μ E ≠ 0) :
--   μ ((λ x, x⁻¹) ⁻¹' E) ≠ 0 :=
-- begin
--   have hf : measurable (λ z : G × G, (z.2 * z.1, z.1⁻¹)) :=
--   ((measurable_snd.mul measurable_fst).prod_mk measurable_fst.inv),
--   have : map (λ z : G × G, (z.2 * z.1, z.1⁻¹)) (μ.prod μ) (E.prod E) ≠ 0,
--   { simp_rw [map_prod_mul_inv_eq hμ hμ, prod_prod hE hE, ← zero_lt_iff_ne_zero, ennreal.mul_pos,
--       and_self, zero_lt_iff_ne_zero], exact h2E },
--   refine mt (λ h, _) this,
--   simp_rw [map_apply hf (hE.prod hE), prod_apply_symm (hf (hE.prod hE)), preimage_preimage,
--     preimage_prod_mk_prod],
--   convert lintegral_zero, ext1 x, refine measure_mono_null (inter_subset_right _ _) h
-- end

lemma measurable_measure_mul_right (hμ : is_left_invariant μ) {E : set G}
  (hE : is_measurable E) : measurable (λ x, μ ((λ y, y * x) ⁻¹' E)) :=
begin
  suffices :
    measurable (λ y, μ ((λ x, (x, y)) ⁻¹' ((λ z : G × G, (1, z.1 * z.2)) ⁻¹' set.prod univ E))),
  { convert this, ext1 x, congr' 1 with y : 1, simp },
  apply measurable_measure_prod_mk_right,
  exact measurable_const.prod_mk (measurable_fst.mul measurable_snd) (is_measurable.univ.prod hE)
end

lemma lintegral_lintegral_mul_inv (hμ : is_left_invariant μ) (hν : is_left_invariant ν)
  (f : G → G → ennreal) (hf : measurable (uncurry f)) :
  ∫⁻ x, ∫⁻ y, f (y * x) x⁻¹ ∂ν ∂μ = ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ :=
begin
  have h2f : measurable (uncurry $ λ x y, f (y * x) x⁻¹) :=
  hf.comp ((measurable_snd.mul measurable_fst).prod_mk measurable_fst.inv),
  simp_rw [lintegral_lintegral h2f, lintegral_lintegral hf],
  conv_rhs { rw [← map_prod_mul_inv_eq hμ hν] },
  symmetry, exact lintegral_map hf ((measurable_snd.mul measurable_fst).prod_mk measurable_fst.inv)
end

lemma measure_mul_right_null (hμ : is_left_invariant μ) {E : set G} (hE : is_measurable E) (y : G) :
  μ ((λ x, x * y) ⁻¹' E) = 0 ↔ μ E = 0 :=
begin
  rw [← measure_inv_null hμ hE, ← hμ y⁻¹ (measurable_inv hE),
    ← measure_inv_null hμ (measurable_mul_right y hE)],
  convert iff.rfl using 3, ext x, simp,
end

lemma measure_mul_right_eq_top (hμ : is_left_invariant μ) {E : set G} (hE : is_measurable E)
  (y : G) : μ ((λ x, x * y) ⁻¹' E) = ⊤ ↔ μ E = ⊤ :=
begin
  rw [← measure_inv_eq_top hμ hE, ← hμ y⁻¹ (measurable_inv hE),
    ← measure_inv_eq_top hμ (measurable_mul_right y hE)],
  convert iff.rfl using 3, ext x, simp,
end

lemma measure_mul_right_ne_zero (hμ : is_left_invariant μ) {E : set G} (hE : is_measurable E)
  (h2E : μ E ≠ 0) (y : G) : μ ((λ x, x * y) ⁻¹' E) ≠ 0 :=
(not_iff_not_of_iff (measure_mul_right_null hμ hE y)).mpr h2E

lemma measure_mul_right_ne_top (hμ : is_left_invariant μ) {E : set G} (hE : is_measurable E)
  (h2E : μ E ≠ ⊤) (y : G) : μ ((λ x, x * y) ⁻¹' E) ≠ ⊤ :=
(not_iff_not_of_iff (measure_mul_right_eq_top hμ hE y)).mpr h2E

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
