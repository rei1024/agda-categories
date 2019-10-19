{-# OPTIONS --without-K --safe #-}

-- The category of Cats is Monoidal

module Categories.Category.Monoidal.Instance.Cats where

open import Level
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; uncurry)

open import Categories.Category
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Category.Instance.Cats
open import Categories.Category.Monoidal
open import Categories.Functor.Bifunctor
open import Categories.Category.Instance.One
open import Categories.Category.Product
open import Categories.Category.Product.Properties
import Categories.Category.Cartesian as Cartesian
open import Categories.NaturalTransformation.NaturalIsomorphism using (NaturalIsomorphism)

open import Categories.Category.CartesianClosed
open import Categories.Category.Construction.Functors
import Categories.Object.Product as OP
open import Categories.Functor.Construction.Constant using (const)

-- Cats is a Monoidal Category with Product as Bifunctor
-- It is also CartesianClosed
module Product {o ℓ e : Level} where
  private
    C = Cats o ℓ e
    open Cartesian C

  Cats-has-all : BinaryProducts
  Cats-has-all = record { product = λ {A} {B} → record
    { A×B = Product A B
    ; π₁ = πˡ
    ; π₂ = πʳ
    ; ⟨_,_⟩ = _※_
    ; project₁ = λ {_} {h} {i} → project₁ {i = h} {j = i}
    ; project₂ = λ {_} {h} {i} → project₂ {i = h} {j = i}
    ; unique = unique
    } }

  Cats-is : Cartesian
  Cats-is = record { terminal = One-⊤ ; products = Cats-has-all }

  private
    module Cart = Cartesian.Cartesian Cats-is

  Cats-Monoidal : Monoidal C
  Cats-Monoidal = Cart.monoidal

-- CartesianClosed is way more restrictive: everything must be at the same level!
module CatsCartesianClosed {o : Level} where
  private
    C = Cats o o o
    open Cartesian C
    module P = Product {o} {o} {o}
    open OP C renaming (Product to OProduct)

  CCC : CartesianClosed C
  CCC = record
    { cartesian = P.Cats-is
    ; exp = λ {A} {B} → record
      { B^A = Functors A B
      ; product = BinaryProducts.product P.Cats-has-all
      ; eval = eval
      ; λg = λg {A} {B}
      ; β = {!β!}
      ; λ-unique = {!!}
      }
    }
    where
      λg : {A₁ A₂ X : Category o o o} → (X×A : OProduct X A₁) →
        (C [ [[ X×A ]] , A₂ ]) → C [ X , Functors A₁ A₂ ]
      λg {A₁} {A₂} {X} X×A F = record
        { F₀ = G₀
        ; F₁ = λ A⇒B → record
          { η = λ _ → F₁ (Functor.F₁ myProd (A⇒B , Category.id A₁))
          ; commute = λ f → {!!}
          }
        ; identity = H₂.trans (F-resp-≈ (Functor.identity myProd)) identity
        ; homomorphism = λ {_} {_} {_} {f} {g} → {!!}
        ; F-resp-≈ = λ {_} {_} {f} {g} f≈g → F-resp-≈ (Functor.F-resp-≈ myProd (f≈g , A₁.Equiv.refl))
        }
        where
        module Q = OProduct X×A
        module X = Category X
        module A₁ = Category A₁
        module A₂ = Category A₂
        module H₂ = A₂.HomReasoning
        open Functor F
        myProd : Functor (Product X A₁) Q.A×B
        myProd = Q.⟨ πˡ , πʳ ⟩
        G₀ : (x : Category.Obj X) → Functor A₁ A₂
        G₀ x = record
          { F₀ = λ a → F₀ (Functor.F₀ myProd (x , a))
          ; F₁ = λ {A₁} {A₂} A₁⇒A₂ → F₁ (Functor.F₁ myProd (X.id , A₁⇒A₂))
          ; identity = begin
            F₁ (Functor.F₁ myProd (X.id , A₁.id)) ≈⟨ F-resp-≈ (Functor.identity myProd) ⟩
            F₁ (Category.id Q.A×B)                ≈⟨ identity ⟩
            Category.id A₂ ∎
          ; homomorphism = {!!}
          ; F-resp-≈ = λ f≈g → F-resp-≈ (Functor.F-resp-≈ myProd (X.Equiv.refl , f≈g))
          }
          where
          open Category.HomReasoning A₂
      β : {A₁ A₂ X : Category o o o } → (X×A : OProduct X A₁) →
          {g : Functor [[ X×A ]] A₂} →
          NaturalIsomorphism (eval ∘F ((λg X×A g ∘F [ X×A ]π₁) ※ (idF ∘F [ X×A ]π₂))) g
      β {A₁} {A₂} {X} X×A {g} = record
        { F⇒G = record
          { η = λ X₁ → Functor.F₁ g {!!}
          ; commute = {!!}
          }
        ; F⇐G = record
          { η = {!!}
          ; commute = {!!}
          }
        ; iso = λ X₁ → record
          { isoˡ = {!!}
          ; isoʳ = {!!}
          }
        }
        where
        open OProduct X×A
        open Category A₂
        module Q = OProduct X×A
        myProd : Functor (Product X A₁) Q.A×B
        myProd = Q.⟨ πˡ , πʳ ⟩
