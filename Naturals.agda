{-# OPTIONS --exact-split #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

module Naturals where

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
 
-- Exercise seven (practice)
seven : ℕ 
seven = 7

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)


-- Exercise +-example (practice)
_ : 3 + 4 ≡ 7
_ = 
    begin
        3 + 4
    ≡⟨⟩
        suc (2 + 4)
    ≡⟨⟩
        suc (suc (1 + 4))
    ≡⟨⟩ 
        suc (suc (suc (0 + 4)))
    ≡⟨⟩
        suc (suc (suc (4)))
    ≡⟨⟩ 
        7
    ∎

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)  

-- Exercise *-example (practice)
_ : 3 * 4 ≡ 12
_ = 
    begin
        3 * 4
    ≡⟨⟩
        4 + (2 * 4)
    ≡⟨⟩
        4 + (4 + (1 * 4))
    ≡⟨⟩
        4 + (4 + (4 + (0 * 4)))
    ≡⟨⟩
        4 + (4 + (4))
    ≡⟨⟩
        12
    ∎

-- Exercise _^_ (recommended)
_^_ : ℕ → ℕ → ℕ
n ^ zero  =  1
m ^ (suc n)  =  m * (m ^ n)

_ : 3 ^ 4 ≡ 81
_ = 
    begin
        3 ^ 4
    ≡⟨⟩
        3 * (3 ^ 3)
    ≡⟨⟩
        3 * (3 * (3 ^ 2))
    ≡⟨⟩
        3 * (3 * (3 * (3 ^ 1)))
    ≡⟨⟩
        3 * (3 * (3 * (3 * (3 ^ 0))))
    ≡⟨⟩
        3 * (3 * (3 * (3)))
    ≡⟨⟩
        81
    ∎

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

-- Exercise ∸-example₁ and ∸-example₂ (recommended)

_ : 5 ∸ 3 ≡ 2
_ = 
    begin
        5 ∸ 3
    ≡⟨⟩
        4 ∸ 2
    ≡⟨⟩
        3 ∸ 1
    ≡⟨⟩
        2 ∸ 0
    ≡⟨⟩
        2
    ∎

_ : 3 ∸ 5 ≡ 0
_ = 
    begin
        3 ∸ 5
    ≡⟨⟩
        2 ∸ 4
    ≡⟨⟩ 
        1 ∸ 3
    ≡⟨⟩ 
        0 ∸ 2
    ≡⟨⟩
        0
    ∎
    

infixl 6  _+_  _∸_
infixl 7  _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = 
    begin
        inc (⟨⟩ I O I I)
    ≡⟨⟩  
        (inc (⟨⟩ I O I)) O
    ≡⟨⟩
        ((inc (⟨⟩ I O)) O) O
    ≡⟨⟩
        ((⟨⟩ I I) O) O
    ≡⟨⟩
        ⟨⟩ I I O O
    ∎

to   : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

_ : to 3 ≡ ⟨⟩ I I
_ = 
    begin 
        to 3
    ≡⟨⟩
        inc (to 2)
    ≡⟨⟩
        inc (inc (to 1))
    ≡⟨⟩
        inc (inc (inc (to 0)))
    ≡⟨⟩
        inc (inc (inc (⟨⟩ O)))
    ≡⟨⟩
        inc (inc (⟨⟩ I))
    ≡⟨⟩ 
        inc ((inc ⟨⟩) O)
    ≡⟨⟩
        inc ((⟨⟩ I) O)
    ≡⟨⟩
        ((⟨⟩ I) I)
    ≡⟨⟩
        ⟨⟩ I I
    ∎
    
from : Bin → ℕ
from ⟨⟩ = 0
from (b O) = (from b) * 2
from (b I) = (from b) * 2 + 1

_ : from (⟨⟩ I I O I I) ≡ 27
_ = 
    begin
        from (⟨⟩ I I O I I)
    ≡⟨⟩
        (from (⟨⟩ I I O I)) * 2 + 1
    ≡⟨⟩
        ((from (⟨⟩ I I O) * 2 + 1)) * 2 + 1
    ≡⟨⟩
        ((((from (⟨⟩ I I)) * 2) * 2 + 1)) * 2 + 1
    ≡⟨⟩
        (((((from (⟨⟩ I)) * 2 + 1) * 2) * 2 + 1)) * 2 + 1
    ≡⟨⟩
        ((((((from (⟨⟩)) * 2 + 1) * 2 + 1) * 2) * 2 + 1)) * 2 + 1
    ≡⟨⟩
        ((((((0) * 2 + 1) * 2 + 1) * 2) * 2 + 1)) * 2 + 1
    ≡⟨⟩
        (((((1) * 2 + 1) * 2) * 2 + 1)) * 2 + 1
    ≡⟨⟩
        ((((3) * 2) * 2 + 1)) * 2 + 1
    ≡⟨⟩
        ((6) * 2 + 1) * 2 + 1
    ≡⟨⟩
        (13) * 2 + 1
    ≡⟨⟩
        27
    ∎    





    

    

   
  
   