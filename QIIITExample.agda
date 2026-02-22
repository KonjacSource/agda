{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude

interleaved mutual 
  data Cx : Type
  data Ty : Cx → Type 
  data Tm : (Γ : Cx) → Ty Γ → Type
  data Sb : Cx → Cx → Type 
  where 

    private variable
      Γ Δ Γ₀ Γ₁ Γ₂ Γ₃ : Cx
      A : Ty Γ
      t a : Tm Γ A
      σ γ δ : Sb Δ Γ

    data Cx where 
      𝟏 : Cx 
      _,_ : (Γ : Cx) → Ty Γ → Cx

    data Sb where 
      id : Sb Γ Γ
      _∘_ : Sb Γ₂ Γ₃ → Sb Γ₁ Γ₂ → Sb Γ₁ Γ₃
      ! : Sb Γ 𝟏
      -- sb₁ : Sb₁ Γ Δ → Sb Γ Δ
      𝐩 : Sb (Γ , A) Γ
      

      id-comp : (γ : Sb Δ Γ) → id ∘ γ ≡ γ
      comp-id : (γ : Sb Δ Γ) → γ ∘ id ≡ γ
      comp-assoc : (γ₀ : Sb Γ₁ Γ₀) (γ₁ : Sb Γ₂ Γ₁) (γ₂ : Sb Γ₃ Γ₂) →
                    γ₀ ∘ (γ₁ ∘ γ₂) ≡ (γ₀ ∘ γ₁) ∘ γ₂
      emp-uniq : (δ : Sb Γ 𝟏) → ! ≡ δ
      
    data Ty where
      _[_] : (A : Ty Γ) (γ : Sb Δ Γ) → Ty Δ

      sub-id : (A : Ty Γ) → A [ id ] ≡ A
      sub-comp : (A : Ty Γ₀) (γ₀ : Sb Γ₁ Γ₀) (γ₁ : Sb Γ₂ Γ₁) → 
                  A [ γ₀ ∘ γ₁ ] ≡ A [ γ₀ ] [ γ₁ ]

    -- Interleaved Sb
    data Sb where 
      _,_ : (γ : Sb Δ Γ) {A : Ty Γ} (a : Tm Δ (A [ γ ])) → Sb Δ (Γ , A)             


    data Tm where
      _[_] : (a : Tm Γ A) (γ : Sb Δ Γ) → Tm Δ (A [ γ ])
      𝐪 : Tm (Γ , A) (A [ 𝐩 ])


      sub-id : {Γ : Cx} {A : Ty Γ} {a : Tm Γ A} → 
                PathP (λ i → congS (Tm Γ) (sub-id A) i) (a [ id ]) a
      sub-comp : {Γ₀ Γ₁ Γ₂ : Cx} {A : Ty Γ₀} {a : Tm Γ₀ A} (γ₀ : Sb Γ₁ Γ₀) (γ₁ : Sb Γ₂ Γ₁) → 
                  PathP (λ i → congS (Tm Γ₂) (sub-comp A γ₀ γ₁) i) (a [ γ₀ ∘ γ₁ ]) (a [ γ₀ ] [ γ₁ ])
      
