import std-lib.Reflection

module Naturals where

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

-- Exercise seven (practice)
seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc (zero)))))))

