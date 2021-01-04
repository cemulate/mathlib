/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Bhavik Mehta
-/
import category_theory.adjunction.basic
import category_theory.conj
import category_theory.yoneda

/-!
# Mate of natural transformations

This file establishes the bijection between the 2-cells

         L₁                  R₁
      C --→ D             C ←-- D
    G ↓  ↗  ↓ H         G ↓  ↘  ↓ H
      E --→ F             E ←-- F
         L₂                  R₂

where `L₁ ⊣ R₁` and `L₂ ⊣ R₂`, and shows that in the special case where `G,H` are identity then the
bijection preserves and reflects isomorphisms (i.e. we have bijections `(L₂ ⟶ L₁) ≃ (R₁ ⟶ R₂)`, and
if either side is an iso then the other side is as well).

On its own, this bijection is not particularly useful but it includes a number of interesting cases
as specializations.

For instance, this generalises the fact that adjunctions are unique (since if `L₁ ≅ L₂` then we
deduce `R₁ ≅ R₂`).
Another example arises from considering the square representing that a functor `H` preserves
products, in particular the morphism `HA ⨯ H- ⟶ H(A ⨯ -)`. Then provided `(A ⨯ -)` and `HA ⨯ -` have
left adjoints (for instance if the relevant categories are cartesian closed), the transferred
natural transformation is the exponential comparison morphism: `H(A ^ -) ⟶ HA ^ H-`.
Furthermore if `H` has a left adjoint `L`, this morphism is an isomorphism iff its mate
`L(HA ⨯ -) ⟶ A ⨯ L-` is an isomorphism, see
https://ncatlab.org/nlab/show/Frobenius+reciprocity#InCategoryTheory.
This also relates to Grothendieck's yoga of six operations, though this is not spelled out in
mathlib: https://ncatlab.org/nlab/show/six+operations.
-/
universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace category_theory
open category

variables {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D]

section square

variables {E : Type u₃} {F : Type u₄} [category.{v₃} E] [category.{v₄} F]

variables (G : C ⥤ E) (H : D ⥤ F) {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
variables (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

include adj₁ adj₂

/--
Suppose we have a square of functors (where the top and bottom are adjunctions `L₁ ⊣ R₁` and
`L₂ ⊣ R₂` respectively).

      C ↔ D
    G ↓   ↓ H
      E ↔ F

Then we have a bijection between natural transformations `G ⋙ L₂ ⟶ L₁ ⋙ H` and
`R₁ ⋙ G ⟶ H ⋙ R₂`.
This can be seen as a bijection of the 2-cells:

         L₁                  R₁
      C --→ D             C ←-- D
    G ↓  ↗  ↓ H         G ↓  ↘  ↓ H
      E --→ F             E ←-- F
         L₂                  R₂

Note that if one of the transformations is an iso, it does not imply the other is an iso.
-/
@[simps]
def transfer_nat_trans : (G ⋙ L₂ ⟶ L₁ ⋙ H) ≃ (R₁ ⋙ G ⟶ H ⋙ R₂) :=
{ to_fun := λ h,
  { app := λ X, adj₂.unit.app _ ≫ R₂.map (h.app _ ≫ H.map (adj₁.counit.app _)),
    naturality' := λ X Y f,
    begin
      dsimp,
      rw [assoc, ← R₂.map_comp, assoc, ← H.map_comp, ← adj₁.counit_naturality, H.map_comp,
          ←functor.comp_map L₁, ←h.naturality_assoc],
      simp,
    end },
  inv_fun := λ h,
  { app := λ X, L₂.map (G.map (adj₁.unit.app _) ≫ h.app _) ≫ adj₂.counit.app _,
  naturality' := λ X Y f,
  begin
    dsimp,
    rw [← L₂.map_comp_assoc, ← G.map_comp_assoc, ← adj₁.unit_naturality, G.map_comp_assoc,
        ← functor.comp_map, h.naturality],
    simp,
  end },
  left_inv := λ h,
  begin
    ext X,
    dsimp,
    simp only [L₂.map_comp, assoc, adj₂.counit_naturality, adj₂.left_triangle_components_assoc,
      ←functor.comp_map G L₂, h.naturality_assoc, functor.comp_map L₁, ←H.map_comp,
      adj₁.left_triangle_components],
    dsimp,
    simp, -- See library note [dsimp, simp].
  end,
  right_inv := λ h,
  begin
    ext X,
    dsimp,
    simp [-functor.comp_map, ←functor.comp_map H, functor.comp_map R₁, -nat_trans.naturality,
      ←h.naturality, -functor.map_comp, ←functor.map_comp_assoc G, R₂.map_comp],
  end }

end square

section self

variables {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/--
Given two adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂` both between categories `C`, `D`, there is a
bijection between natural transformations `L₂ ⟶ L₁` and natural transformations `R₁ ⟶ R₂`.
This is defined as a special case of `transfer_nat_trans`, where the two "vertical" functors are
identity.
TODO: Generalise to when the two vertical functors are equivalences rather than being exactly `𝟭`.

Furthermore, this bijection preserves (and reflects) isomorphisms, i.e. a transformation is an iso
iff its image under the bijection is an iso, see eg `category_theory.transfer_nat_trans_self_iso`.
This is in contrast to the general case `transfer_nat_trans` which does not in general have this
property.
-/
@[simps {rhs_md := semireducible}]
def transfer_nat_trans_self : (L₂ ⟶ L₁) ≃ (R₁ ⟶ R₂) :=
calc (L₂ ⟶ L₁) ≃ _         : (iso.hom_congr L₂.left_unitor L₁.right_unitor).symm
           ... ≃ _         : transfer_nat_trans (𝟭 _) (𝟭 _) adj₁ adj₂
           ... ≃ (R₁ ⟶ R₂) : R₁.right_unitor.hom_congr R₂.left_unitor

lemma transfer_nat_trans_self_comm {f g} (gf : g ≫ f = 𝟙 _) :
  transfer_nat_trans_self adj₁ adj₂ f ≫ transfer_nat_trans_self adj₂ adj₁ g = 𝟙 _ :=
begin
  ext,
  dsimp,
  simp only [id_comp, comp_id],
  rw [←adj₁.unit_naturality_assoc, ←R₁.map_comp, g.naturality_assoc, L₂.map_comp, assoc,
    adj₂.counit_naturality, adj₂.left_triangle_components_assoc, ← assoc, ← nat_trans.comp_app],
  simp [gf],
end

lemma transfer_nat_trans_self_symm_comm {f g} (gf : g ≫ f = 𝟙 _) :
  (transfer_nat_trans_self adj₁ adj₂).symm f ≫ (transfer_nat_trans_self adj₂ adj₁).symm g = 𝟙 _ :=
begin
  ext,
  dsimp,
  simp only [id_comp, comp_id],
  rw [assoc, ←adj₂.counit_naturality, ←L₂.map_comp_assoc, assoc, ←f.naturality, R₁.map_comp, assoc,
    adj₁.unit_naturality_assoc, assoc, adj₁.right_triangle_components_assoc, ← nat_trans.comp_app],
  simp [gf],
end

/--
If `f` is an isomorphism, then the transferred natural transformation is an isomorphism.
The converse is given in `transfer_nat_trans_self_of_iso`.
-/
instance transfer_nat_trans_self_iso (f : L₂ ⟶ L₁) [is_iso f] :
  is_iso (transfer_nat_trans_self adj₁ adj₂ f) :=
{ inv := transfer_nat_trans_self adj₂ adj₁ (inv f),
  hom_inv_id' := transfer_nat_trans_self_comm _ _ (by simp),
  inv_hom_id' := transfer_nat_trans_self_comm _ _ (by simp) }

/--
If `f` is an isomorphism, then the un-transferred natural transformation is an isomorphism.
The converse is given in `transfer_nat_trans_self_symm_of_iso`.
-/
instance transfer_nat_trans_self_symm_iso (f : R₁ ⟶ R₂) [is_iso f] :
  is_iso ((transfer_nat_trans_self adj₁ adj₂).symm f) :=
{ inv := (transfer_nat_trans_self adj₂ adj₁).symm (inv f),
  hom_inv_id' := transfer_nat_trans_self_symm_comm _ _ (by simp),
  inv_hom_id' := transfer_nat_trans_self_symm_comm _ _ (by simp) }

/--
If `f` is a natural transformation whose transferred natural transformation is an isomorphism,
then `f` is an isomorphism.
The converse is given in `transfer_nat_trans_self_iso`.
-/
def transfer_nat_trans_self_of_iso (f : L₂ ⟶ L₁) [is_iso (transfer_nat_trans_self adj₁ adj₂ f)] :
  is_iso f :=
begin
  suffices :
    is_iso ((transfer_nat_trans_self adj₁ adj₂).symm (transfer_nat_trans_self adj₁ adj₂ f)),
  { simpa using this },
  apply_instance,
end

/--
If `f` is a natural transformation whose un-transferred natural transformation is an isomorphism,
then `f` is an isomorphism.
The converse is given in `transfer_nat_trans_self_symm_iso`.
-/
def transfer_nat_trans_self_symm_of_iso (f : R₁ ⟶ R₂)
  [is_iso ((transfer_nat_trans_self adj₁ adj₂).symm f)] :
  is_iso f :=
begin
  suffices :
    is_iso ((transfer_nat_trans_self adj₁ adj₂) ((transfer_nat_trans_self adj₁ adj₂).symm f)),
  { simpa using this },
  apply_instance,
end

end self

end category_theory
