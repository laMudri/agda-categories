{-# OPTIONS --without-K --safe #-}

module Categories.Multi.Category.Cartesian.Representable where

open import Data.List hiding ([_])
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Unary.Any
import Data.List.Relation.Unary.Any.Properties as AnyP
open import Data.Product
open import Data.Sum
open import Data.Wrap
open import Function.Base as F using (case_return_of_)
open import Level
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open import Categories.Category
open import Categories.Category.Cartesian
import Categories.Category.Cartesian.Properties as ×P
open import Categories.Multi.Category.Cartesian

private
  variable
    o ℓ e : Level

module Extras {a} {A : Set a} where
  -- TODO: contribute to stdlib

  ∈-++⁺ : ∀ {x : A} {xs ys} (i : x ∈ xs ⊎ x ∈ ys) → x ∈ xs ++ ys
  ∈-++⁺ = [ ∈-++⁺ˡ , ∈-++⁺ʳ _ ]′

  ∈-++⁻∘++⁺ˡ : ∀ {x : A} {xs} ys (i : x ∈ xs) → ∈-++⁻ xs {ys} (∈-++⁺ˡ i) ≡ inj₁ i
  ∈-++⁻∘++⁺ˡ {xs = xs} ys i = AnyP.++⁻∘++⁺ xs (inj₁ i)

  ∈-++⁻∘++⁺ʳ : ∀ {x : A} xs {ys} (i : x ∈ ys) → ∈-++⁻ xs (∈-++⁺ʳ xs i) ≡ inj₂ i
  ∈-++⁻∘++⁺ʳ xs i = AnyP.++⁻∘++⁺ xs (inj₂ i)

  ∈-++⁺∘++⁻ : ∀ {x : A} xs {ys} (i : x ∈ xs ++ ys) → ∈-++⁺ (∈-++⁻ xs i) ≡ i
  ∈-++⁺∘++⁻ xs i = AnyP.++⁺∘++⁻ xs i

module _ {C : Category o ℓ e} (cart : Cartesian C) where

  open Category C
  open Equiv
  open HomReasoning
  open Cartesian cart
  open ×P C
  open Prods cart

  Fam : Obj → List Obj → Set (o ⊔ ℓ)
  Fam X Δ = ∀ {Y} → Y ∈ Δ → X ⇒ Y

  ⟨_⟩Π : ∀ {X Δ} → Fam X Δ → X ⇒ prod Δ
  ⟨_⟩Π {Δ = []} fs = !
  ⟨_⟩Π {Δ = Y ∷ Δ} fs = ⟨ fs (here ≡.refl) , ⟨ fs F.∘ there ⟩Π ⟩

  ⟨_⟩Π-resp-≈ : ∀ {X Δ} {fs gs : Fam X Δ} →
    (∀ {Y} (i : Y ∈ Δ) → fs i ≈ gs i) → ⟨ fs ⟩Π ≈ ⟨ gs ⟩Π
  ⟨_⟩Π-resp-≈ {Δ = []} ps = refl
  ⟨_⟩Π-resp-≈ {Δ = Y ∷ Δ} ps =
    ⟨⟩-cong₂ (ps (here ≡.refl)) ⟨ ps F.∘ there ⟩Π-resp-≈

  projectΠ : ∀ {X Y Δ} (i : Y ∈ Δ) (fs : Fam X Δ) → π[ i ] ∘ ⟨ fs ⟩Π ≈ fs i
  projectΠ (here ≡.refl) fs = project₁
  projectΠ (there i) fs =
    trans assoc (trans (∘-resp-≈ refl project₂) (projectΠ i _))

  ⟨π⟩Π : ∀ {Γ} → ⟨ π[_] {_} {Γ} ⟩Π ≈ id
  ⟨π⟩Π {Γ} = uniqueness* {ys = Γ} λ i → trans (projectΠ i _) (sym identityʳ)

  Rep : CartesianMultiCategory o ℓ e
  Rep = record
    { Obj = Obj
    ; _⇒_ = λ Γ A → prod Γ ⇒ A
    ; _≈_ = _≈_
    ; id = π[_]
    ; _∘_ = λ f σ → f ∘ ⟨ σ ⟩Π
    ; equiv = equiv
    ; ∘-resp-≈ = λ ff σσ → ∘-resp-≈ ff ⟨ σσ .get ⟩Π-resp-≈
    ; identityˡ = λ {_} {_} {_} {i} → projectΠ i _
    ; identityʳ = λ {Γ} → trans (∘-resp-≈ʳ (⟨π⟩Π {Γ})) identityʳ
    ; identity² = λ {_} {_} {i} → projectΠ i _
    ; assoc = λ {Γ Δ Θ A f σ τ} → begin
      (f ∘ ⟨ σ ⟩Π) ∘ ⟨ τ ⟩Π  ≈⟨ assoc ⟩
      f ∘ (⟨ σ ⟩Π ∘ ⟨ τ ⟩Π)
        ≈⟨ refl⟩∘⟨ (uniqueness* {ys = Θ} λ i → begin
        π[ i ] ∘ ⟨ σ ⟩Π ∘ ⟨ τ ⟩Π  ≈⟨ sym-assoc ⟩
        (π[ i ] ∘ ⟨ σ ⟩Π) ∘ ⟨ τ ⟩Π  ≈⟨ projectΠ i _ ⟩∘⟨refl ⟩
        σ i ∘ ⟨ τ ⟩Π  ≈˘⟨ projectΠ i _ ⟩
        π[ i ] ∘ ⟨ (λ j → σ j ∘ ⟨ τ ⟩Π) ⟩Π  ∎) ⟩
      f ∘ ⟨ (λ i → σ i ∘ ⟨ τ ⟩Π) ⟩Π  ∎
    ; sym-assoc = λ {Γ Δ Θ A f σ τ} → begin
      f ∘ ⟨ (λ i → σ i ∘ ⟨ τ ⟩Π) ⟩Π
        ≈⟨ refl⟩∘⟨ (uniqueness* {ys = Θ} λ i → begin
        π[ i ] ∘ ⟨ (λ j → σ j ∘ ⟨ τ ⟩Π) ⟩Π  ≈⟨ projectΠ i _ ⟩
        σ i ∘ ⟨ τ ⟩Π  ≈˘⟨ projectΠ i _ ⟩∘⟨refl ⟩
        (π[ i ] ∘ ⟨ σ ⟩Π) ∘ ⟨ τ ⟩Π  ≈⟨ assoc ⟩
        π[ i ] ∘ ⟨ σ ⟩Π ∘ ⟨ τ ⟩Π  ∎) ⟩
      f ∘ (⟨ σ ⟩Π ∘ ⟨ τ ⟩Π)  ≈⟨ sym-assoc ⟩
      (f ∘ ⟨ σ ⟩Π) ∘ ⟨ τ ⟩Π  ∎
    }

module _ (CM : CartesianMultiCategory o ℓ e) where
  open CartesianMultiCategory CM
  open Equiv
  open Equivˢ

  Free : ∃ \ C → Cartesian C
  Free = record
    { fst = record
      { Obj = List Obj
      ; _⇒_ = _⇒ˢ_
      ; _≈_ = _≈ˢ_
      ; id = idˢ
      ; _∘_ = _∘ˢ_
      ; assoc = assocˢ
      ; sym-assoc = sym-assocˢ
      ; identityˡ = identityˡˢ
      ; identityʳ = identityʳˢ
      ; identity² = identity²ˢ
      ; equiv = record { refl = reflˢ ; sym = symˢ ; trans = transˢ }
      ; ∘-resp-≈ = ∘ˢ-resp-≈
      }
    ; snd = record
      { terminal = record
        { ⊤ = []
        ; ⊤-is-terminal = record { ! = λ () ; !-unique = λ { σ .get () } }
        }
      ; products = record
        { product = λ {Γ Δ} → record
          { A×B = Γ ++ Δ
          ; π₁ = λ i → id (∈-++⁺ˡ i)
          ; π₂ = λ i → id (∈-++⁺ʳ Γ i)
          ; ⟨_,_⟩ = λ σ τ i → [ σ , τ ]′ (∈-++⁻ Γ i)
          ; project₁ = λ { .get i →
            trans identityˡ (reflexive (≡.cong [ _ , _ ]′ (∈-++⁻∘++⁺ˡ Δ i))) }
          ; project₂ = λ { .get i →
            trans identityˡ (reflexive (≡.cong [ _ , _ ]′ (∈-++⁻∘++⁺ʳ Γ i))) }
          ; unique = unique
          }
        }
      }
    }
    where
    open Extras

    unique : ∀ {Γ Δ Θ} {f : Θ ⇒ˢ (Γ ++ Δ)} {g : Θ ⇒ˢ Γ} {h : Θ ⇒ˢ Δ} →
      (λ j → id (∈-++⁺ˡ j)) ∘ˢ f ≈ˢ g →
      (λ k → id (∈-++⁺ʳ Γ k)) ∘ˢ f ≈ˢ h →
      (λ i → [ g , h ]′ (∈-++⁻ Γ i)) ≈ˢ f
    unique {Γ} p q .get i with ∈-++⁻ Γ i | ∈-++⁺∘++⁻ Γ i
    ... | inj₁ j | ≡.refl = trans (sym (p .get j)) identityˡ
    ... | inj₂ k | ≡.refl = trans (sym (q .get k)) identityˡ