{-
This isn't really an agda file, it's just easier to type stuff with Agda mode available
sometimes.

On List and Bag:
- the container List can be represented (amongst other things) as Σ ℕ Fin
- the containg Bag can be represented as Σ ℕ (λ n → Σ Set (λ A → ∥ A ≃ Fin n ∥ ) )
- List is also Σ ℕ (λ n → Σ Set (λ A → A ≃ Fin n) )
  (where it is implicit that Fin n can be given an ordering)

- I think that Bag is also  Σ ℕ (λ n → Σ Set (λ A → Aut A ≡ Sₙ ) )
-}
