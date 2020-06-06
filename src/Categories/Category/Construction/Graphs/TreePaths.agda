{-# OPTIONS --without-K --safe --postfix-projections #-}

module Categories.Category.Construction.Graphs.TreePaths where

open import Function.Base as F using (flip; _on_)
open import Level
open import Relation.Binary using (Rel; IsEquivalence)
import Relation.Binary.Construct.On as On

open import Categories.Category
open import Categories.Category.Equivalence
  using (StrongEquivalence; WeakInverse)
open import Categories.Functor using (Functor)
open import Categories.NaturalTransformation.NaturalIsomorphism
  using (NaturalIsomorphism; niHelper)
open import Categories.NaturalTransformation
  using (NaturalTransformation)
-- open import Categories.Category.Construction.Graphs using (Graph)

module _ {i} {I : Set i} where

  private
    variable
      w x y z : I

  infix 5 _∙_

  data TStar {t} (T : Rel I t) : Rel I (i ⊔ t) where
    [_] : (f : T x y) → TStar T x y
    ε : TStar T x x
    _∙_ : TStar T x y → TStar T y z → TStar T x z

module _ {o ℓ e} (C : Category o ℓ e) where
  open Category
  open Equiv C

  private
    variable
      x y z : C .Obj

  ⟦_⟧ : TStar (C [_,_]) x y → C [ x , y ]
  ⟦ [ f ] ⟧ = f
  ⟦ ε ⟧ = C .id
  ⟦ p ∙ q ⟧ = C ._∘_ ⟦ q ⟧ ⟦ p ⟧

  pathify : Category o (o ⊔ ℓ) e
  pathify .Obj = C .Obj
  pathify ._⇒_ = TStar (C [_,_])
  pathify ._≈_ = C ._≈_ on ⟦_⟧
  pathify .id = ε
  pathify ._∘_ = flip _∙_
  pathify .assoc = C .assoc
  pathify .sym-assoc = C .sym-assoc
  pathify .identityˡ = C .identityˡ
  pathify .identityʳ = C .identityʳ
  pathify .identity² = C .identity²
  pathify .equiv = On.isEquivalence ⟦_⟧ (C .equiv)
  pathify .∘-resp-≈ fh gi = C .∘-resp-≈ fh gi

  open StrongEquivalence
  open Functor
  open WeakInverse
  open NaturalIsomorphism
  open NaturalTransformation

  pathify-equiv : StrongEquivalence C pathify
  pathify-equiv .F .F₀ = F.id
  pathify-equiv .F .F₁ = [_]
  pathify-equiv .F .identity = refl
  pathify-equiv .F .homomorphism = refl
  pathify-equiv .F .F-resp-≈ = F.id
  pathify-equiv .G .F₀ = F.id
  pathify-equiv .G .F₁ = ⟦_⟧
  pathify-equiv .G .identity = refl
  pathify-equiv .G .homomorphism = refl
  pathify-equiv .G .F-resp-≈ = F.id
  pathify-equiv .weak-inverse .F∘G≈id = niHelper record
    { η = λ _ → ε
    ; η⁻¹ = λ _ → ε
    ; commute = λ _ → trans (C .identityˡ) (sym (C .identityʳ))
    ; iso = λ _ → record
      { isoˡ = C .identity²
      ; isoʳ = C .identity²
      }
    }
  pathify-equiv .weak-inverse .G∘F≈id = niHelper record
    { η = λ _ → C .id
    ; η⁻¹ = λ _ → C .id
    ; commute = λ _ → trans (C .identityˡ) (sym (C .identityʳ))
    ; iso = λ _ → record
      { isoˡ = C .identity²
      ; isoʳ = C .identity²
      }
    }
