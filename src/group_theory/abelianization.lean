/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Michael Howes

The functor Grp → Ab which is the left adjoint
of the forgetful functor Ab → Grp.
-/

-- TODO:
-- (1) Abelian groups solvable ✓
-- (2) Quotients of solvable groups solvable ✓
-- (3) Subgroups of solvable groups solvable ✓
-- (4) If G is in the middle of a short exact sequence with everything else solvable
--     then G is solvable
-- (5) S_5 is not solvable (A_5 is simple)

-- Small todos:
-- (1) Show that the subgroup generated by the commutators is equal to its normal closure ✓

import group_theory.quotient_group
import tactic.group
import group_theory.perm.sign
import set_theory.cardinal
open subgroup


universes u v

-- let G be a group
variables (G : Type u) [group G]

section commutator

/-- The commutator subgroup of a group G is the normal subgroup
  generated by the commutators [p,q]=`p*q*p⁻¹*q⁻¹` -/
@[derive subgroup.normal]
def commutator : subgroup G :=
normal_closure {x | ∃ p q, p * q * p⁻¹ * q⁻¹ = x}

variables {G}

def general_commutator (H₁ : subgroup G) (H₂ : subgroup G) : subgroup G :=
subgroup.closure {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x}

instance general_commutator_normal (H₁ : subgroup G) (H₂ : subgroup G) [h₁ : H₁.normal]
  [h₂ : H₂.normal] : normal (general_commutator H₁ H₂) :=
begin
  let base : set G := {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x},
  suffices h_base : base = group.conjugates_of_set base,
  { dsimp only [general_commutator, ←base],
    rw h_base,
    exact subgroup.normal_closure_normal },
  apply set.subset.antisymm group.subset_conjugates_of_set,
  intros a h,
  rw group.mem_conjugates_of_set_iff at h,
  rcases h with ⟨b, ⟨c, hc, e, he, rfl⟩, d, rfl⟩,
  exact ⟨d * c * d⁻¹, h₁.conj_mem c hc d, d * e * d⁻¹, h₂.conj_mem e he d, by group⟩,
end

lemma general_commutator_eq_normal_closure (H₁ : subgroup G) (H₂ : subgroup G) [H₁.normal]
  [H₂.normal] : general_commutator H₁ H₂ = normal_closure (general_commutator H₁ H₂) :=
eq.symm normal_closure_eq_self_of_normal

lemma general_commutator_eq_normal_closure' (H₁ H₂ : subgroup G) [H₁.normal] [H₂.normal] :
  general_commutator H₁ H₂ = normal_closure {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x} :=
by rw [general_commutator_eq_normal_closure, general_commutator,
  normal_closure_closure_eq_normal_closure]

lemma general_commutator_mono {H₁ H₂ K₁ K₂ : subgroup G} (h₁ : H₁ ≤ K₁) (h₂ : H₂ ≤ K₂) :
  general_commutator H₁ H₂ ≤ general_commutator K₁ K₂ :=
begin
  apply closure_mono,
  rintros x ⟨p, hp, q, hq, rfl⟩,
  exact ⟨p, h₁ hp, q, h₂ hq, rfl⟩,
end

section nth_commutator

variables (G)

def nth_commutator (n : ℕ) : subgroup G :=
nat.rec_on n (⊤ : subgroup G) (λ _ H, general_commutator H H)

def general_nth_commutator (G':subgroup G)(n:ℕ): subgroup G:=
nat.rec_on n (G' : subgroup G) (λ _ H, general_commutator H H)



instance top_normal: (⊤: subgroup G).normal :=
{ conj_mem :=  λ  n mem g, mem_top (g*n *g⁻¹ ), }

lemma nth_commutator_normal (n : ℕ) : (nth_commutator G n).normal :=
begin
  induction n with n ih,
  { change (⊤ : subgroup G).normal,
    exact top_normal G, },
  { haveI : (nth_commutator G n).normal := ih,
    change (general_commutator (nth_commutator G n) (nth_commutator G n)).normal,
    exact general_commutator_normal (nth_commutator G n) (nth_commutator G n), }
end

lemma commutator_eq_general_commutator_top_top :
  commutator G = general_commutator (⊤ : subgroup G) (⊤ : subgroup G) :=
begin
  rw commutator,
  rw general_commutator_eq_normal_closure',
  apply le_antisymm; apply normal_closure_mono,
  { exact λ x ⟨p, q, h⟩, ⟨p, mem_top p, q, mem_top q, h⟩, },
  { exact λ x ⟨p, _, q, _, h⟩, ⟨p, q, h⟩, }
end

lemma commutator_def' : commutator G = subgroup.closure {x : G | ∃ p q, p * q * p⁻¹ * q⁻¹ = x} :=
begin
  rw commutator_eq_general_commutator_top_top,
  rw general_commutator,
  apply le_antisymm; apply closure_mono,
  { exact λ x ⟨p, _, q, _, h⟩, ⟨p, q, h⟩ },
  { exact λ x ⟨p, q, h⟩, ⟨p, mem_top p, q, mem_top q, h⟩ }
end

@[simp] lemma nth_commutator_zero : nth_commutator G 0 = ⊤ := rfl
lemma general_nth_commutator_subgroup (G':subgroup G): (general_nth_commutator G G' (0:ℕ) ) = G':=
rfl

@[simp] lemma nth_commutator_one : nth_commutator G 1 = commutator G :=
eq.symm $ commutator_eq_general_commutator_top_top G

lemma general_nth_commutator_succ (G':subgroup G)(n:ℕ ): general_nth_commutator G G' (nat.succ n) =
general_commutator (general_nth_commutator G G' n) (general_nth_commutator G G' n):=rfl


lemma general_nth_commutator_one (G':subgroup G): general_nth_commutator G G' 1 =
general_commutator G' G':=
begin
  rw [general_nth_commutator_succ,general_nth_commutator_subgroup],

end



--lemma isomorphism (H: subgroup G)(K:subgroup H):general_commutator H H = (general_commutator H (⊤:subgroup H) H).lift:=sorry

lemma nth_commutator_succ (n : ℕ) :
  nth_commutator G (n + 1) = general_commutator (nth_commutator G n) (nth_commutator G n) := rfl

lemma nth_commutator_eq_general_nth_commutator_if_top : nth_commutator G=general_nth_commutator G (⊤:subgroup G):=
begin
  funext,
  induction n,
  rw [nth_commutator_zero,general_nth_commutator_subgroup],
  rw [nth_commutator_succ,general_nth_commutator_succ, n_ih],
end

variables {G} {G' : Type*} [group G'] {f : G →* G'}

lemma map_commutator_eq_commutator_map (H₁ H₂ : subgroup G) :
  (general_commutator H₁ H₂).map f = general_commutator (H₁.map f) (H₂.map f) :=
begin
  rw [general_commutator, general_commutator, monoid_hom.map_closure],
  apply le_antisymm; apply closure_mono,
  { rintros _ ⟨x, ⟨p, hp, q, hq, rfl⟩, rfl⟩,
    refine ⟨f p, mem_map.mpr ⟨p, hp, rfl⟩, f q, mem_map.mpr ⟨q, hq, rfl⟩, by simp *⟩, },
  { rintros x ⟨_, ⟨p, hp, rfl⟩, _, ⟨q, hq, rfl⟩, rfl⟩,
    refine ⟨p * q * p⁻¹ * q⁻¹, ⟨p, hp, q, hq, rfl⟩, by simp *⟩, },
end

--lemma nth_commutator_eq_nth_commutator_map (n:ℕ) :
--(nth_commutator G n).map f= (nth_commutator ((⊤:subgroup G).map f) n):=sorry

lemma lift_commutator_eq_commutator_lift_lift {H : subgroup G} (K₁ K₂ : subgroup H) :
  (general_commutator K₁ K₂).lift = general_commutator (K₁.lift) (K₂.lift) :=
map_commutator_eq_commutator_map _ _

lemma nth_commutator_lift_eq_general_nth_commutator {H : subgroup G} (n:ℕ) :
  (nth_commutator H n).lift = general_nth_commutator G H n:=
  begin
    induction n,
    rw [nth_commutator_zero,general_nth_commutator_subgroup],
    by tidy,
    rw [nth_commutator_succ,general_nth_commutator_succ,
    lift_commutator_eq_commutator_lift_lift, n_ih],
    sorry,
  end
#check subgroup.lift_top

lemma commutator_le_commutator_map {H₁ H₂ : subgroup G} {K₁ K₂ : subgroup G'} (h₁ : K₁ ≤ H₁.map f)
  (h₂ : K₂ ≤ H₂.map f) : general_commutator K₁ K₂ ≤ (general_commutator H₁ H₂).map f :=
begin
  rw map_commutator_eq_commutator_map,
  exact general_commutator_mono h₁ h₂,
end

lemma map_nth_commutator_le_nth_commutator (n : ℕ) :
  (nth_commutator G n).map f ≤ nth_commutator G' n :=
begin
  induction n with n ih,
  { simp only [nth_commutator_zero, le_top], },
  { simp only [nth_commutator_succ, map_commutator_eq_commutator_map, general_commutator_mono, *], }
end

lemma nth_commutator_le_map_nth_commutator (hf : function.surjective f) (n : ℕ) :
  nth_commutator G' n ≤ (nth_commutator G n).map f :=
begin
  induction n with n ih,
  { rwa [nth_commutator_zero, nth_commutator_zero, top_le_iff, ← monoid_hom.range_eq_map,
    ← monoid_hom.range_top_iff_surjective.mpr], },
  { simp only [*, nth_commutator_succ, commutator_le_commutator_map], }
end

lemma nth_commutator_eq_map_nth_commutator (hf : function.surjective f) (n : ℕ) :
  nth_commutator G' n = (nth_commutator G n).map f :=
le_antisymm (nth_commutator_le_map_nth_commutator hf n) (map_nth_commutator_le_nth_commutator n)

lemma nth_commutator_lift_le_nth_commutator (H : subgroup G) (n : ℕ) :
  (nth_commutator H n).lift ≤ nth_commutator G n :=
map_nth_commutator_le_nth_commutator n

end nth_commutator

end commutator

/-- The abelianization of G is the quotient of G by its commutator subgroup -/
def abelianization : Type u :=
quotient_group.quotient (commutator G)

namespace abelianization

local attribute [instance] quotient_group.left_rel

instance : comm_group (abelianization G) :=
{ mul_comm := λ x y, quotient.induction_on₂' x y $ λ a b,
  begin
    apply quotient.sound,
    apply subset_normal_closure,
    use b⁻¹, use a⁻¹,
    group,
  end,
.. quotient_group.quotient.group _ }

instance : inhabited (abelianization G) := ⟨1⟩

variable {G}

/-- `of` is the canonical projection from G to its abelianization. -/
def of : G →* abelianization G :=
{ to_fun := quotient_group.mk,
  map_one' := rfl,
  map_mul' := λ x y, rfl }

section lift
-- so far -- built Gᵃᵇ and proved it's an abelian group.
-- defined `of : G → Gᵃᵇ`

-- let A be an abelian group and let f be a group hom from G to A
variables {A : Type v} [comm_group A] (f : G →* A)

lemma commutator_subset_ker : commutator G ≤ f.ker :=
begin
  apply normal_closure_le_normal,
  rintros x ⟨p, q, rfl⟩,
  simp [monoid_hom.mem_ker, mul_right_comm (f p) (f q)],
end

/-- If `f : G → A` is a group homomorphism to an abelian group, then `lift f` is the unique map from
  the abelianization of a `G` to `A` that factors through `f`. -/
def lift : abelianization G →* A :=
quotient_group.lift _ f (λ x h, f.mem_ker.2 $ commutator_subset_ker _ h)

@[simp] lemma lift.of (x : G) : lift f (of x) = f x :=
rfl

theorem lift.unique
  (φ : abelianization G →* A)
  -- hφ : φ agrees with f on the image of G in Gᵃᵇ
  (hφ : ∀ (x : G), φ (of x) = f x)
  {x : abelianization G} :
  φ x = lift f x :=
quotient_group.induction_on x hφ

end lift

variables {A : Type v} [monoid A]

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem hom_ext (φ ψ : abelianization G →* A)
  (h : φ.comp of = ψ.comp of) : φ = ψ :=
begin
  ext x,
  apply quotient_group.induction_on x,
  intro z,
  show φ.comp of z = _,
  rw h,
  refl,
end

end abelianization

section solvable

def is_solvable : Prop := ∃ n : ℕ, nth_commutator G n = (⊥ : subgroup G)

lemma is_solvable_of_comm {G : Type*} [comm_group G] : is_solvable G :=
begin
  use 1,
  rw [eq_bot_iff, nth_commutator_one],
  calc commutator G ≤ (monoid_hom.id G).ker : abelianization.commutator_subset_ker (monoid_hom.id G)
  ... = ⊥ : rfl,
end

variables {G}

theorem subgroup_solvable_of_solvable (H : subgroup G) (h : is_solvable G) : is_solvable H :=
begin
  cases h with n h,
  use n,
  rw eq_bot_iff_lift_eq_bot,
  rw eq_bot_iff at *,
  calc (nth_commutator H n).lift ≤ nth_commutator G n : nth_commutator_lift_le_nth_commutator H n
  ... ≤ ⊥ : h,
end

variables {G' : Type*} [group G'] {f : G →* G'}

lemma solvable_image_of_solvable (hf : function.surjective f) (h : is_solvable G) :
  is_solvable G' :=
begin
  cases h with n hn,
  use n,
  calc nth_commutator G' n = (nth_commutator G n).map f : nth_commutator_eq_map_nth_commutator hf n
    ... = (⊥ : subgroup G).map f : by rw hn
    ... = ⊥ : map_bot f,
end

lemma solvable_quotient_of_solvable (H : subgroup G) [H.normal] (h : is_solvable G) :
  is_solvable (quotient_group.quotient H) :=
solvable_image_of_solvable (show function.surjective (quotient_group.mk' H), by tidy) h

open quotient_group

--this theorem (and its proof) is due to Mario

theorem eq_top_of_trivial_quotient (N:subgroup G) [N.normal]
(H : (⊤ : subgroup (quotient_group.quotient N)) ≤ ⊥) :
 N = ⊤ :=
begin
  rw [← ker_mk N, eq_top_iff, monoid_hom.ker, ← subgroup.map_le_iff_le_comap],
  exact le_trans le_top H,
end

--(ker_mk N).symm.trans $ eq_top_iff.2 $ subgroup.map_le_iff_le_comap.1 $ le_trans le_top H


lemma quotient_something (H : subgroup G) [H.normal]
(h':is_solvable (quotient_group.quotient H)): ∃ m:ℕ, (nth_commutator G m)≤ H:=
begin
  unfold is_solvable at h',
  cases h' with paris france,
  use paris,

  have surj:function.surjective (quotient_group.mk' H),
  convert surjective_quot_mk setoid.r,
  have image: nth_commutator (quotient H) paris=(nth_commutator G paris).map (quotient_group.mk' H),
  apply nth_commutator_eq_map_nth_commutator surj,
  rw france at image,
  suffices: ↑(nth_commutator G paris) ⊆ ↑H,
  exact coe_subset_coe.mp this,
  intros x x_in,

  --it seems like this should follow from image in one line
  have bound:(mk' H) x ∈ (⊥:subgroup (quotient H)),
  simp *,
  use x,
  split,
  exact x_in,
  simp only [eq_self_iff_true],
  have reduction:(mk' H) x=(mk' H) 1,
  simp[bound],
  exact mem_bot.mp bound,
  rw  subgroup.set.has_coe,
  have triv_mem':=subgroup.one_mem H,
  have triv_mem: (1:G)∈ ↑ H,
  exact mem_coe.mpr triv_mem',
  have s:= @quotient_group.eq G _inst_1 H 1 x,
  have small:1⁻¹ * x=x,
  simp only [one_inv, one_mul],
  rw small at s,
  apply s.1,
  have hmmmm:↑(1:G)=mk (1:G),
  exact (rfl.congr bound).mp (eq.symm bound),
  have hmmmmmmmm:↑ x=mk x,
  exact (rfl.congr (eq.symm bound)).mp bound,
  change (mk) x=(mk) 1 at reduction,
  symmetry,
  rwa [hmmmm,hmmmmmmmm],
end
inductive weekday : Type
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday

lemma weekday_perm_unsolvable:¬ is_solvable (equiv.perm weekday):=
begin
  unfold is_solvable,
  push_neg,
end



lemma lift_subgroup_eq_subgroup (H: subgroup G):(⊤:subgroup H).lift=H:=
begin
  --change (⊤:subgroup H).map (subtype H) = H,
  apply subgroup.partial_order.le_antisymm,
  --library_search!,
  --rw ←  subgroup.coe_subset_coe,

  intros x x_in,
  have s:(⊤:subgroup H).lift = (⊤:subgroup H).map (subtype H):=rfl,
  rw s at x_in,
  --have t: ∃ y∈ H, x= y.map,




  --change x∈( (⊤:subgroup H).map (subtype G)) at x_in,
  have zeta:= (@subgroup.mem_lift G _inst_1 ⊤  H),
  --change x∈ ↑ H,

  --change ∃ y∈ H, x= (↑y:G),
  --have xi:=@subgroup.mem_lift G _inst_1 H,
  specialize zeta ⟨ x,mem_top x⟩,
  --have w: (⊤:subgroup H).lift = (⊤:subgroup H).map (subtype H):=rfl,
  --rw w at x_in,
  --simp *,
  sorry,


end
lemma mem_lift (H:subgroup G)(K : subgroup H) (x : H) : x ∈ K ↔ ↑x ∈ K.lift :=
begin
  rcases x with ⟨x, hx⟩,
  exact ⟨λ h, ⟨⟨x, hx⟩, h, rfl⟩, λ _, by tidy⟩,
end

lemma short_exact_sequence_solvable (H : subgroup G) [H.normal]
(h : is_solvable H) (h':is_solvable (quotient_group.quotient H)): is_solvable G:=
begin
  have reduction:=quotient_something H h',
  unfold is_solvable at h,
  cases h with n n_solves,
  cases reduction with m m_solves,
  use n+m,
  sorry,

end

--def alternating_group (X:Type u)[fintype X]:Type u:=(equiv.perm.sign X).ker

--instance (X:Type u)[fintype X]: group((equiv.perm.sign X).ker)

lemma unsolvability_of_S_5 (X:Type u)(big:5≤ cardinal.mk X)[fintype X]:¬ is_solvable (equiv.perm X):=
begin
  --have x:=X.elems.val.to_list,
  unfold is_solvable,
  push_neg,
  have moscow:=_inst_3.elems,
  have russia:=_inst_3.complete,
  let delhi:=fintype.elems X,
  let paris:=(delhi).val,
  have france:=(delhi).nodup,
  have u: list X,
  exact list.nil,


  rw cardinal.le_mk_iff_exists_set at big,
  cases big with big_subset florida,
  --have v:cardinal.mk big_subset<cardinal.omega,
  --apply cardinal.lt_omega.2,
  --use 5,

  --exact florida,

  --have u: fintype big_subset,
  --apply fintype.of_equiv,
  have w:fintype.card ↥big_subset=5,

  --library_search,


  have equiv: nonempty((fin 5)≃ big_subset),

  apply fintype.card_eq.1,


  --library_search!,
  --have first: ∃ x_1,x_1∈ big_subset,

end


end solvable
