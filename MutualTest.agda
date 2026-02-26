-- {-# OPTIONS --cubical #-}
{-# OPTIONS -WnoUnreachableClauses #-}
-- open import Cubical.Core.Everything
o7 : (a : Set) → a → a 
o7 _ x = x

interleaved mutual
  data AA : Set
  data BB : AA → Set
  where

    data AA where
      a : AA

    data BB where
      b : BB a

    data AA where
      f : BB a → AA
      g : BB (f b) → AA

    data BB where
      h : (x : BB a) → BB (f x)


module _ (AAᴹ : AA → Set) (BBᴹ : ∀ {x} → AAᴹ x → BB x → Set)
         (aᴹ : AAᴹ a) (fᴹ : ∀ {x} → BBᴹ aᴹ x → AAᴹ (f x))
         (bᴹ : BBᴹ aᴹ b)
         (gᴹ : ∀ {x} → BBᴹ (fᴹ bᴹ) x → AAᴹ (g x))
         (hᴹ : ∀ {x} (xᴹ : BBᴹ aᴹ x) → BBᴹ (fᴹ xᴹ) (h x)) 
         where

  interleaved mutual 
  
    elimA : ∀ x → AAᴹ x 
    elimB : ∀ {x} (y : BB x) → BBᴹ (elimA x) y
    where
      elimA a     = aᴹ
      
      elimB b     = bᴹ
      
      elimA (f x) = fᴹ (elimB x)
      elimA (g x) = gᴹ (elimB x) 

      elimB (h y) = hᴹ (elimB y)

