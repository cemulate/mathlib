/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.comma
import category_theory.elements
import category_theory.filtered
import category_theory.limits.shapes.finite_limits
import category_theory.limits.shapes.types
import category_theory.limits.presheaf
import category_theory.limits.filtered_colimit_commutes_finite_limit2
import category_theory.limits.preserves.limits
import category_theory.limits.preserves.shapes.terminal
import category_theory.limits.preserves.shapes.binary_products
import category_theory.limits.preserves.shapes.equalizers

/-!
# Flat functors

A typeclass for functors which are flat.
-/

universes w v₁ v₂ u₁ u₂

namespace category_theory
open opposite limits

variables {C : Type u₁} [category.{v₁} C]
variables {D : Type u₂} [category.{v₂} D]

/-- The functor `F : C ⥤ Type` is set-valued flat iff its category of elements is cofiltered. -/
abbreviation is_set_flat (F : C ⥤ Type w) := is_filtered F.elementsᵒᵖ

/--
The functor `F : C ⥤ D` is flat iff, for each `d` in `D`, the composite `C ⟶ D ⟶ Type v₂` given
by `F ⋙ coyoneda.obj d` is set-valued flat.
Note that if `C` does not have finite limits, this can be in general stronger than `F : C ⥤ Type w`
being set-valued flat.
-/
abbreviation is_flat (F : C ⥤ D) := ∀ (d : D), is_set_flat (F ⋙ coyoneda.obj (op d))

variables (F : C ⥤ D) (d : D)

-- def equiv_set_flat :
--   comma (functor.from_punit d) F ≌ (F ⋙ coyoneda.obj (op d)).elements :=
-- equivalence.mk
--   { obj := λ p, ⟨p.right, p.hom⟩,
--     map := λ p₁ p₂ α, ⟨α.right, α.w.symm.trans (category.id_comp _)⟩ }
--   { obj := λ p,
--     { left := punit.star, right := p.1, hom := p.2 },
--     map := λ _ _ α,
--     { left := eq_to_hom rfl, right := α.1, w' := eq.trans (category.id_comp _) α.2.symm, } }
--   (nat_iso.of_components (λ p, eq_to_iso (by { cases p, tidy })) (by { rintro ⟨⟩ ⟨⟩, tidy }))
--   (nat_iso.of_components (λ p, eq_to_iso (by tidy)) (by tidy))

/--
Prop 6.1.2 (1) => (2) of (Borceux)
-/
def set_flat_of_preserves_finite_limits [has_finite_limits.{v₁} C] (F : C ⥤ Type v₁)
  [∀ (J : Type v₁) [𝒥 : small_category J] [@fin_category J 𝒥],
      @preserves_limits_of_shape _ _ _ _ J 𝒥 F] :
  is_set_flat F :=
{ nonempty := ⟨op ⟨⊤_ C, (is_limit_of_has_terminal_of_preserves_limit F).from punit punit.star⟩⟩,
  cocone_objs := λ X Y,
  begin
    refine ⟨op ⟨X.unop.1 ⨯ Y.unop.1, _⟩, _, _, ⟨⟩⟩,
    { apply (((types.binary_product_iso_prod.app _).app _).hom ≫
                  inv (prod_comparison F X.unop.1 Y.unop.1)) ⟨X.unop.2, Y.unop.2⟩ },
    { refine has_hom.hom.op (_ : _ ⟶ unop X),
      refine ⟨limits.prod.fst, _⟩,
      dsimp only,
      rw [← types_comp_apply _ (F.map _), category.assoc, inv_prod_comparison_map_fst],
      simp [-types_comp_apply] },
    { refine has_hom.hom.op (_ : _ ⟶ unop Y),
      refine ⟨limits.prod.snd, _⟩,
      dsimp only,
      rw [← types_comp_apply _ (F.map _), category.assoc, inv_prod_comparison_map_snd],
      simp [-types_comp_apply] },
  end,
  cocone_maps := λ X Y f g,
  begin
    refine ⟨op ⟨equalizer f.unop.1 g.unop.1, _⟩, _, _⟩,
    { apply inv (equalizer_comparison f.unop.1 g.unop.1 F) _,
      apply (types.equalizer_limit.is_limit.cone_point_unique_up_to_iso (limit.is_limit _)).hom,
      refine ⟨Y.unop.2, _⟩,
      rw [f.unop.2, g.unop.2] },
    { refine has_hom.hom.op (_ : _ ⟶ unop Y),
      refine ⟨equalizer.ι _ _, _⟩,
      dsimp only,
      rw [← types_comp_apply _ (inv (equalizer_comparison f.unop.val g.unop.val F)),
          ← types_comp_apply _ (F.map (equalizer.ι f.unop.val g.unop.val)), category.assoc,
          inv_equalizer_comparison_comp_map],
      simp [-types_comp_apply] },
    { apply has_hom.hom.unop_inj,
      apply subtype.ext,
      apply equalizer.condition }
  end }.

@[simps {rhs_md := semireducible}]
def my_functor (F : C ⥤ Type v₁) : F.elementsᵒᵖ ⥤ C ⥤ Type v₁ :=
functor.op (category_of_elements.π F) ⋙ coyoneda

@[simps]
def alt_cocone (F : C ⥤ Type v₁) :
  cocone (my_functor F) :=
{ X := F,
  ι :=
  { app := λ p,
    { app := λ Y f, F.map f p.unop.2,
      naturality' := λ Y₁ Y₂ g,
      begin
        ext f,
        apply functor_to_types.map_comp_apply F f g,
      end },
    naturality' := λ p₁ p₂ α,
    begin
      ext X x,
      change F.map (α.unop.1 ≫ x) _ = F.map _ _,
      rw [functor_to_types.map_comp_apply F, α.unop.2],
    end } }

def alt_colimit (F : C ⥤ Type v₁) :
  is_colimit (alt_cocone F) :=
{ desc := λ s,
  { app := λ X t, (s.ι.app (op ⟨X, t⟩)).app _ (𝟙 _),
    naturality' :=
    begin
      intros X Y f,
      ext t,
      let X' : F.elementsᵒᵖ := op ⟨X, t⟩,
      let Y' : F.elementsᵒᵖ := op ⟨Y, F.map f t⟩,
      let f' : Y' ⟶ X' := has_hom.hom.op ⟨_, rfl⟩,
      change (s.ι.app Y').app _ (𝟙 Y) = s.X.map f ((s.ι.app X').app _ _),
      rw ← s.w f',
      change (s.ι.app X').app Y (f ≫ 𝟙 Y) = ((s.ι.app X').app X ≫ s.X.map f) (𝟙 X),
      rw category.comp_id,
      rw ← (show _ = (s.ι.app X').app X ≫ s.X.map f, from (s.ι.app X').naturality f),
      change _ = (s.ι.app X').app Y (𝟙 X ≫ f),
      rw category.id_comp f,
    end },
  fac' := λ s j,
  begin
    op_induction j,
    cases j with X x,
    ext Y f,
    let X' : F.elementsᵒᵖ := op ⟨X, x⟩,
    let Y' : F.elementsᵒᵖ := op ⟨Y, F.map f x⟩,
    let f' : Y' ⟶ X' := has_hom.hom.op ⟨_, rfl⟩,
    change (s.ι.app Y').app Y (𝟙 Y) = (s.ι.app X').app Y f,
    rw ← s.w f',
    dsimp,
    simp,
  end,
  uniq' :=  λ s m w,
  begin
    ext X x,
    change m.app X x = (s.ι.app (op ⟨X, x⟩)).app X (𝟙 X),
    rw ← w (op ⟨X, x⟩),
    dsimp,
    simp,
  end }

set_option pp.universes true

-- F : C.{v u} => Type w
-- F.elements : homs in v, objs in max u w
-- max u w = w
def preserves_finite_limits_of_set_flat {C : Type u₁} [category.{v₁} C]
  [has_finite_limits C] (F : C ⥤ Type v₁)
[is_set_flat F] (J : Type v₁) [category.{w} J] [fin_category J] :
preserves_limits_of_shape J F :=
{ preserves_limit := λ K,
  { preserves := λ c t,
    begin
      let Γ : F.elementsᵒᵖ ⥤ J ⥤ Type v₁ :=
        (category_of_elements.π F).op ⋙ coyoneda ⋙ (whiskering_left J C _).obj K,
      -- have := alt_colimit F,
      -- have := F.elementsᵒᵖ,
      have := @filtered_colimit_finite_limit_iso _ _ _ _ Γ,
      -- let Γ : F.elementsᵒᵖ × J ⥤ Type v₁ := (category_of_elements.π F).op.prod K ⋙ functor.hom C,

      -- apply functor.prod _ _ ⋙ functor.hom C,
      -- have : has_colimits_of_shape (F.elementsᵒᵖ) (Type v₁),

      -- have := alt_colimit F,
      -- have := colimit (my_functor F),
      -- have := category_theory.limits.functor_category_has_colimits_of_shape,

      -- let X := limit (K ⋙ F),
      -- let θ := functor.op (category_of_elements.π F),
      -- have := colimit_limit_to_limit_colimit,

      -- let F' := (op_op_equivalence C).functor ⋙ F,
      -- have := colimit_of_representable F',
      -- have := colimit_of_representable,
    end } }

-- def is_set_flat_of_is_flat (F : C ⥤ Type w) [is_flat F] : is_set_flat F :=
-- begin
--   change is_filtered _,

-- end

-- { functor :=
--   { obj := λ p, ⟨p.right, p.hom⟩,
--     map := λ p₁ p₂ α, ⟨α.right, α.w.symm.trans (category.id_comp _)⟩ },
--   inverse :=
--   { obj := λ p,
--     { left := punit.star, right := p.1, hom := p.2 },
--     map := λ p₁ p₂ α,
--     { left := eq_to_hom rfl, right := α.1, w' := eq.trans (category.id_comp _) α.2.symm, } },
--   unit_iso :=
--   begin
--     refine nat_iso.of_components _ _,
--     { intro p,
--       apply comma.iso_mk _ _ _,
--       { apply eq_to_iso _,
--         apply subsingleton.elim },
--       { apply iso.refl _ },
--       { tidy },
--     },
--     { intros p₁ p₂ α,
--       ext,
--       simp }
--   end,
--   counit_iso := nat_iso.of_components (λ p, eq_to_iso (by tidy)) (by tidy) }

lemma is_filtered_of_equiv (h : C ≌ D)
[hC : is_filtered C] : is_filtered D :=
{
  cocone_objs :=
  λ X Y, let ⟨Z,f,g,_⟩ :=
  is_filtered_or_empty.cocone_objs (h.inverse.obj X) (h.inverse.obj Y) in
  ⟨h.functor.obj Z,(h.counit_inv.app X) ≫ (h.functor.map f),(h.counit_inv.app Y)
  ≫ (h.functor.map g),trivial⟩,
  cocone_maps := λ X Y f g,
  let ⟨Z,z,zz⟩ :=
  is_filtered_or_empty.cocone_maps (h.inverse.map f) (h.inverse.map g) in
  ⟨h.functor.obj Z,(h.counit_inv.app Y) ≫ (h.functor.map z),sorry⟩,
  nonempty := nonempty.map h.functor.obj hC.nonempty
}

lemma is_filtered_of (T : C) (hT : is_terminal T) :
is_filtered C :=
{ cocone_objs := λ X Y, ⟨T,hT.from X,hT.from Y,trivial⟩,
  cocone_maps := λ X Y f g, ⟨T,hT.from Y,hT.hom_ext _ _⟩,
  nonempty := ⟨T⟩ }

def elements.initial2 (A : C) : (coyoneda.obj (op A)).elements :=
⟨A, 𝟙 _⟩

def is_initial2 (A : C) : is_initial (elements.initial2 A) :=
{ desc := λ s, ⟨s.X.2, category.id_comp _⟩,
  uniq' := λ s m w,
  begin
    simp_rw ← m.2,
    dsimp [elements.initial2],
    simp,
  end }

lemma representable_is_set_flat (U : C) :
is_filtered (coyoneda.obj(op U)).elementsᵒᵖ :=
is_filtered_of (op (elements.initial2 U)) (terminal_op_of_initial (is_initial2 U))

end category_theory
